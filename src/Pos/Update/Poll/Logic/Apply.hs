{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Logic of application and verification of data in Poll.

module Pos.Update.Poll.Logic.Apply
       ( verifyAndApplyUSPayload
       , verifyAndApplyProposal
       , verifyAndApplyVoteDo
       ) where

import           Control.Monad.Except       (MonadError, throwError)
import           Data.List                  (partition)
import           Data.List.NonEmpty         (NonEmpty)
import qualified Data.List.NonEmpty         as NE
import           Formatting                 (build, builder, int, sformat, (%))
import           System.Wlog                (logDebug, logInfo, logNotice)
import           Universum

import           Pos.Constants              (blkSecurityParam, genesisUpdateImplicit,
                                             genesisUpdateProposalThd,
                                             genesisUpdateVoteThd)
import           Pos.Crypto                 (hash, shortHashF)
import           Pos.Ssc.Class              (Ssc)
import           Pos.Types                  (ChainDifficulty, Coin, EpochIndex,
                                             HeaderHash, MainBlockHeader,
                                             SlotId (siEpoch), SoftwareVersion (..),
                                             addressHash, applyCoinPortion, coinToInteger,
                                             difficultyL, epochIndexL, flattenSlotId,
                                             gbhExtra, headerHash, headerSlot,
                                             mehBlockVersion, sumCoins, unflattenSlotId,
                                             unsafeIntegerToCoin)
import           Pos.Update.Core            (BlockVersionData (..), UpId,
                                             UpdatePayload (..), UpdateProposal (..),
                                             UpdateVote (..), upMaxBlockSize,
                                             upScriptVersion, upSlotDuration)
import           Pos.Update.Poll.Class      (MonadPoll (..), MonadPollRead (..))
import           Pos.Update.Poll.Failure    (PollVerFailure (..))
import           Pos.Update.Poll.Logic.Base (canBeAdoptedBV, canBeProposedBV,
                                             canCreateBlockBV, confirmBlockVersion,
                                             isDecided, mkTotNegative, mkTotPositive,
                                             mkTotSum, putNewProposal, verifyNextBVData,
                                             voteToUProposalState)
import           Pos.Update.Poll.Types      (BlockVersionState (..),
                                             ConfirmedProposalState (..),
                                             DecidedProposalState (..), DpsExtra (..),
                                             ProposalState (..),
                                             UndecidedProposalState (..), UpsExtra (..))

type ApplyMode m = (MonadError PollVerFailure m, MonadPoll m)

-- | Verify UpdatePayload with respect to data provided by
-- MonadPoll. If data is valid it is also applied.  Otherwise
-- PollVerificationFailure is thrown using MonadError type class.
-- When first flag is true and proposal is present,
-- 'genesisUpdateProposalThd' is checked for it, otherwise it's not
-- checked.
-- When second argument is 'Left epoch', it means that temporary payload
-- for given slot is applied.
-- When it is 'Right header', it means that payload from block with
-- given header is applied.
verifyAndApplyUSPayload
    :: forall ssc m . (ApplyMode m, Ssc ssc)
    => Bool -> Either SlotId (MainBlockHeader ssc) -> UpdatePayload -> m ()
verifyAndApplyUSPayload considerPropThreshold slotOrHeader UpdatePayload {..} = do
    -- First of all, we verify data from header.
    either (const pass) verifyHeader slotOrHeader
    -- Then we split all votes into groups. One group consists of
    -- votes for proposal from payload. Each other group consists of
    -- votes for other proposals.
    let upId = hash <$> upProposal
    let votePredicate vote = maybe False (uvProposalId vote ==) upId
    let (curPropVotes, otherVotes) = partition votePredicate upVotes
    let otherGroups = NE.groupWith uvProposalId otherVotes
    -- When there is proposal in payload, it's verified and applied.
    whenJust
        upProposal
        (verifyAndApplyProposal considerPropThreshold slotOrHeader curPropVotes)
    -- Then we also apply votes from other groups.
    -- ChainDifficulty is needed, because proposal may become approved
    -- and then we'll need to track whether it becomes confirmed.
    let cd = (,) <$> either (const Nothing) (Just . view difficultyL) slotOrHeader
                 <*> either (const Nothing) (Just . headerHash) slotOrHeader
    mapM_ (verifyAndApplyVotesGroup cd) otherGroups
    -- If we are applying payload from block, we also check implicit
    -- agreement rule and depth of decided proposals (they can become
    -- confirmed/discarded).
    case slotOrHeader of
        Left _ -> pass
        Right mainBlk -> do
            applyImplicitAgreement
                (mainBlk ^. headerSlot)
                (mainBlk ^. difficultyL)
                (headerHash mainBlk)
            applyDepthCheck
                (headerHash mainBlk)
                (mainBlk ^. difficultyL)

-- Here we verify all US-related data from header.
verifyHeader
    :: (MonadError PollVerFailure m, MonadPoll m)
    => MainBlockHeader __ -> m ()
verifyHeader header = do
    lastAdopted <- getAdoptedBV
    let versionInHeader = header ^. gbhExtra ^. mehBlockVersion
    unlessM (canCreateBlockBV versionInHeader) $
        throwError
            PollWrongHeaderBlockVersion
            {pwhpvGiven = versionInHeader, pwhpvAdopted = lastAdopted}

-- Get stake of stakeholder who issued given vote as per given epoch.
-- If stakeholder wasn't richman at that point, PollNotRichman is thrown.
resolveVoteStake
    :: (MonadError PollVerFailure m, MonadPollRead m)
    => EpochIndex -> Coin -> UpdateVote -> m Coin
resolveVoteStake epoch totalStake UpdateVote {..} = do
    let !id = addressHash uvKey
    stake <- note (mkNotRichman id Nothing) =<< getRichmanStake epoch id
    when (stake < threshold) $ throwError $ mkNotRichman id (Just stake)
    return stake
  where
    threshold = applyCoinPortion genesisUpdateVoteThd totalStake
    mkNotRichman id stake =
        PollNotRichman
        {pnrStakeholder = id, pnrThreshold = threshold, pnrStake = stake}

-- Do all necessary checks of new proposal and votes for it.
-- If it's valid, apply. Specifically, these checks are done:
--
-- 1. Check that there is no active proposal for given application.
-- 2. Check script version, it should be consistent with existing
--    script version dependencies. New dependency can be added.
-- 3. Check that numeric software version of application is 1 more than
--    of last confirmed proposal for this application.
-- 4. If 'considerThreshold' is true, also check that sum of positive votes
--    for this proposal is enough (at least 'genesisUpdateProposalThd').
--
-- If all checks pass, proposal is added. It can be in undecided or decided
-- state (if it has enough voted stake at once).
verifyAndApplyProposal
    :: forall ssc m.
       (MonadError PollVerFailure m, MonadPoll m, Ssc ssc)
    => Bool
    -> Either SlotId (MainBlockHeader ssc)
    -> [UpdateVote]
    -> UpdateProposal
    -> m ()
verifyAndApplyProposal considerThreshold slotOrHeader votes up@UpdateProposal {..} = do
    let epoch = slotOrHeader ^. epochIndexL
    let !upId = hash up
    -- Here we verify consistency with regards to data from 'BlockVersionState'
    -- and update relevant state if necessary.
    verifyAndApplyProposalBVS upId up
    -- Then we verify that protocol version from proposal can follow last adopted software version.
    verifyBlockVersion upId up
    -- We also verify that software version is expected one.
    verifySoftwareVersion upId up
    -- After that we resolve stakes of all votes.
    totalStake <- note (PollUnknownStakes epoch) =<< getEpochTotalStake epoch
    votesAndStakes <-
        mapM (\v -> (v, ) <$> resolveVoteStake epoch totalStake v) votes
    -- When necessary, we also check that proposal itself has enough
    -- positive votes to be included into block.
    when considerThreshold $ verifyProposalStake totalStake votesAndStakes upId
    -- Finally we put it into context of MonadPoll together with votes for it.
    putNewProposal slotOrHeader totalStake votesAndStakes up

-- Here we add check that block version data from proposal is consistent
-- with current data and add new 'BlockVersionState' if this is a new
-- version.
--
-- The following checks are performed:
--
-- 1. We check that versions and constants from proposal are the same as
-- versions and constants from other proposals with the same block version.
--
-- 2. But if the proposal has a new 'BlockVersion', we check that
-- a) its 'ScriptVersion' is @lastScriptVersion + 1@, and
-- b) its 'maxBlockSize' is at most 2× the previous block size.
verifyAndApplyProposalBVS
    :: (MonadError PollVerFailure m, MonadPoll m)
    => UpId -> UpdateProposal -> m ()
verifyAndApplyProposalBVS upId up =
    getBVD >>= \case
        -- This block version is already known, so we just check that
        -- everything is the same
        Just BlockVersionData {..}
            | bvdScriptVersion /= upScriptVersion up -> throwError
                  PollWrongScriptVersion
                      { pwsvExpected = bvdScriptVersion
                      , pwsvFound    = upScriptVersion up
                      , pwsvUpId     = upId }
            | bvdSlotDuration /= upSlotDuration up -> throwError
                  PollWrongSlotDuration
                      { pwsdExpected = bvdSlotDuration
                      , pwsdFound    = upSlotDuration up
                      , pwsdUpId     = upId }
            | bvdMaxBlockSize /= upMaxBlockSize up -> throwError
                  PollWrongMaxBlockSize
                      { pwmbsExpected = bvdMaxBlockSize
                      , pwmbsFound    = upMaxBlockSize up
                      , pwmbsUpId     = upId }
            | otherwise -> pass
        -- This block version isn't known, so we can add it after doing
        -- checks against the previous known block version state
        Nothing -> do
            let bvd = upBlockVersionData up
            let newBVS = BlockVersionState
                  { bvsData = bvd
                  , bvsIsConfirmed   = False
                  , bvsIssuersStable = mempty
                  , bvsIssuersUnstable = mempty
                  , bvsLastBlockStable = Nothing
                  , bvsLastBlockUnstable = Nothing
                  }
            oldBVD <- getAdoptedBVData
            verifyNextBVData upId oldBVD bvd
            putBVState (upBlockVersion up) newBVS
  where
    proposedBV = upBlockVersion up
    getBVD =
        maybe tryAdoptedBVD (pure . Just . bvsData) =<< getBVState proposedBV
    tryAdoptedBVD =
        getAdoptedBVFull <&> \case
            (bv, bvd)
                | bv == proposedBV -> Just bvd
                | otherwise -> Nothing

-- Here we check that software version is 1 more than last confirmed
-- version of given application. Or 0 if it's new application.
verifySoftwareVersion
    :: (MonadError PollVerFailure m, MonadPollRead m)
    => UpId -> UpdateProposal -> m ()
verifySoftwareVersion upId UpdateProposal {..} =
    getLastConfirmedSV app >>= \case
        -- If there is no confirmed versions for given application,
        -- We check that version is 0.
        Nothing | svNumber sv == 0 -> pass
                | otherwise ->
                  throwError
                    PollWrongSoftwareVersion
                    { pwsvStored = Nothing
                    , pwsvGiven = svNumber sv
                    , pwsvApp = app
                    , pwsvUpId = upId
                    }
        -- Otherwise we check that version is 1 more than stored
        -- version.
        Just n
            | svNumber sv == n + 1 -> pass
            | otherwise ->
                throwError
                    PollWrongSoftwareVersion
                    { pwsvStored = Just n
                    , pwsvGiven = svNumber sv
                    , pwsvApp = app
                    , pwsvUpId = upId
                    }
  where
    sv = upSoftwareVersion
    app = svAppName sv

-- Here we verify that proposed protocol version could be proposed.
-- See documentation of 'Logic.Base.canBeProposedBV' for details.
verifyBlockVersion
    :: (MonadError PollVerFailure m, MonadPollRead m)
    => UpId -> UpdateProposal -> m ()
verifyBlockVersion upId UpdateProposal {..} = do
    lastAdopted <- getAdoptedBV
    unlessM (canBeProposedBV upBlockVersion) $
        throwError
            PollBadBlockVersion
            { pbpvUpId = upId
            , pbpvGiven = upBlockVersion
            , pbpvAdopted = lastAdopted
            }

-- Here we check that proposal has at least 'genesisUpdateProposalThd'
-- stake of total stake in all positive votes for it.
verifyProposalStake
    :: (MonadPollRead m, MonadError PollVerFailure m)
    => Coin -> [(UpdateVote, Coin)] -> UpId -> m ()
verifyProposalStake totalStake votesAndStakes upId = do
    let threshold = applyCoinPortion genesisUpdateProposalThd totalStake
    let thresholdInt = coinToInteger threshold
    let votesSum =
            sumCoins . map snd . filter (uvDecision . fst) $ votesAndStakes
    logDebug $
        sformat
            ("Verifying stake for proposal "%shortHashF%
             ", threshold is "%int%", voted stake is "%int)
            upId thresholdInt votesSum
    when (votesSum < thresholdInt) $
        throwError
            PollSmallProposalStake
            { pspsThreshold = threshold
            , pspsActual = unsafeIntegerToCoin votesSum
            , pspsUpId = upId
            }

-- Here we verify votes for proposal which is already active. Each
-- vote must have enough stake as per distribution from epoch where
-- proposal was added.
-- We also verify that what votes correspond to real proposal in
-- undecided state.
-- Votes are assumed to be for the same proposal.
verifyAndApplyVotesGroup
    :: ApplyMode m
    => Maybe (ChainDifficulty, HeaderHash) -> NonEmpty UpdateVote -> m ()
verifyAndApplyVotesGroup cd votes = mapM_ verifyAndApplyVote votes
  where
    upId = uvProposalId $ NE.head votes
    verifyAndApplyVote vote = do
        let !stakeholderId = addressHash . uvKey $ NE.head votes
            unknownProposalErr =
                PollUnknownProposal
                {pupStakeholder = stakeholderId, pupProposal = upId}
        ps <- note unknownProposalErr =<< getProposal upId
        case ps of
            PSDecided _     -> throwError $ PollProposalIsDecided upId stakeholderId
            PSUndecided ups -> verifyAndApplyVoteDo cd ups vote

-- Here we actually apply vote to stored undecided proposal.
verifyAndApplyVoteDo
    :: ApplyMode m
    => Maybe (ChainDifficulty, HeaderHash)
    -> UndecidedProposalState
    -> UpdateVote
    -> m ()
verifyAndApplyVoteDo cd ups v@UpdateVote {..} = do
    let e = siEpoch $ upsSlot ups
    totalStake <- note (PollUnknownStakes e) =<< getEpochTotalStake e
    voteStake <- resolveVoteStake e totalStake v
    newUPS@UndecidedProposalState {..} <-
        voteToUProposalState uvKey voteStake uvDecision ups
    let newPS
            | Just decision <-
                 isDecided
                     (mkTotPositive upsPositiveStake)
                     (mkTotNegative upsNegativeStake)
                     (mkTotSum totalStake) =
                PSDecided
                    DecidedProposalState
                    { dpsUndecided = newUPS
                    , dpsDecision = decision
                    , dpsDifficulty = fst <$> cd
                    , dpsExtra = DpsExtra . snd <$> cd <*> Just False
                    }
            | otherwise = PSUndecided newUPS
    addActiveProposal newPS

-- According to implicit agreement rule all proposals which were put
-- into blocks earlier than 'genesisUpdateImplicit' slots before slot
-- of current block become implicitly decided (approved or rejected).
-- If proposal's total positive stake is bigger than negative, it's
-- approved. Otherwise it's rejected.
applyImplicitAgreement
    :: MonadPoll m
    => SlotId -> ChainDifficulty -> HeaderHash -> m ()
applyImplicitAgreement (flattenSlotId -> slotId) cd hh
    | slotId < genesisUpdateImplicit = pass
    | otherwise = do
        let oldSlot = unflattenSlotId $ slotId - genesisUpdateImplicit
        mapM_ applyImplicitAgreementDo =<< getOldProposals oldSlot
  where
    applyImplicitAgreementDo ups = do
        let decided = makeImplicitlyDecided ups
        addActiveProposal $ PSDecided decided
        let upId = hash $ upsProposal ups
            status | dpsDecision decided = "approved"
                   | otherwise = "rejected"
        logInfo $ sformat ("Proposal "%build%" is implicitly "%builder)
            upId status
    makeImplicitlyDecided ups@UndecidedProposalState {..} =
        DecidedProposalState
        { dpsUndecided = ups
        , dpsDecision = upsPositiveStake > upsNegativeStake
        , dpsDifficulty = Just cd
        , dpsExtra = Just $ DpsExtra hh True
        }

-- All decided proposals which became decided more than
-- 'blkSecurityParam' blocks deeper than current block become
-- confirmed or discarded (approved become confirmed, rejected become
-- discarded).
applyDepthCheck
    :: ApplyMode m
    => HeaderHash -> ChainDifficulty -> m ()
applyDepthCheck hh cd
    | cd <= blkSecurityParam = pass
    | otherwise = do
        deepProposals <- getDeepProposals (cd - blkSecurityParam)
        mapM_ applyDepthCheckDo deepProposals
  where
    applyDepthCheckDo DecidedProposalState {..} = do
        let UndecidedProposalState {..} = dpsUndecided
        let sv = upSoftwareVersion upsProposal
        let bv = upBlockVersion upsProposal
        let upId = hash upsProposal
        let status | dpsDecision = "confirmed"
                   | otherwise = "discarded"
        when dpsDecision $ do
            setLastConfirmedSV sv
            DpsExtra {..} <-
                note (PollInternalError "DPS extra: expected Just, but got Nothing")
                      dpsExtra
            UpsExtra {..} <-
                note (PollInternalError "UPS extra: expected Just, but got Nothing")
                      upsExtra
            let cps = ConfirmedProposalState
                    { cpsUpdateProposal = upsProposal
                    , cpsVotes = upsVotes
                    , cpsPositiveStake = upsPositiveStake
                    , cpsNegativeStake = upsNegativeStake
                    , cpsImplicit = deImplicit
                    , cpsProposed = ueProposedBlk
                    , cpsDecided = deDecidedBlk
                    , cpsConfirmed = hh
                    , cpsAdopted = Nothing
                    }
            addConfirmedProposal cps
        needConfirmBV <- (dpsDecision &&) <$> canBeAdoptedBV bv
        if | needConfirmBV -> do
               confirmBlockVersion bv
               logInfo $ sformat (build%" is competing now") bv
           | otherwise -> do
               delBVState bv
               logInfo $ sformat ("State of "%build%" is deleted") bv
        deactivateProposal (hash upsProposal)
        logNotice $ sformat ("Proposal "%shortHashF%" is "%builder) upId status
