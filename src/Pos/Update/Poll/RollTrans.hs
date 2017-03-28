{-# LANGUAGE Rank2Types #-}
-- | Proxy transformer for tracking updates for
-- rollback. Single-threaded.

module Pos.Update.Poll.RollTrans
       ( RollT (..)
       , runRollT
       , execRollT
       ) where

import           Control.Lens              ((%=), (.=))
import           Control.Monad.Except      (MonadError (..))
import           Control.Monad.Trans.Class (MonadTrans)
import           Data.Default              (def)
import qualified Data.HashMap.Strict       as HM
import qualified Data.List                 as List (find)
import           System.Wlog               (CanLog, HasLoggerName)
import           Universum

import           Pos.Crypto                (hash)

import           Pos.Core.Types            (SoftwareVersion (..))
import           Pos.Update.Poll.Class     (MonadPoll (..), MonadPollRead (..))
import           Pos.Update.Poll.Types     (PrevValue, USUndo (..), cpsSoftwareVersion,
                                            maybeToPrev, psProposal, unChangedBVL,
                                            unChangedConfPropsL, unChangedPropsL,
                                            unChangedSVL, unLastAdoptedBVL,
                                            unPrevProposersL)

newtype RollT m a = RollT
    { getRollT :: StateT USUndo m a
    } deriving ( Functor, Applicative, Monad, MonadThrow
               , HasLoggerName, CanLog
               , MonadTrans, MonadError e)

instance MonadPollRead m => MonadPollRead (RollT m)

-- | Monad transformer which stores USUndo and implements writable
-- MonadPoll. Its purpose is to collect data necessary for rollback.
--
-- [WARNING] This transformer uses StateT and is intended for
-- single-threaded usage only.
instance MonadPoll m => MonadPoll (RollT m) where
    putBVState bv sv = RollT $ do
        insertIfNotExist bv unChangedBVL getBVState
        putBVState bv sv

    delBVState bv = RollT $ do
        insertIfNotExist bv unChangedBVL getBVState
        delBVState bv

    setAdoptedBV pv = RollT $ do
        prevBV <- getAdoptedBV
        whenNothingM_ (use unLastAdoptedBVL) $
            unLastAdoptedBVL .= Just prevBV
        setAdoptedBV pv

    setLastConfirmedSV sv@SoftwareVersion{..} = RollT $ do
        insertIfNotExist svAppName unChangedSVL getLastConfirmedSV
        setLastConfirmedSV sv

    -- can't be called during apply
    delConfirmedSV = lift . delConfirmedSV

    addConfirmedProposal cps = RollT $ do
        confProps <- getConfirmedProposals
        insertIfNotExist (cpsSoftwareVersion cps) unChangedConfPropsL (getter confProps)
        addConfirmedProposal cps
      where
        getter confs sv = pure $ List.find (\x -> cpsSoftwareVersion x == sv) confs

    -- can't be called during apply
    delConfirmedProposal = lift . delConfirmedProposal

    addActiveProposal ps = RollT $ do
        whenNothingM_ (use unPrevProposersL) $ do
            prev <- getEpochProposers
            unPrevProposersL .= Just prev
        insertIfNotExist (hash $ psProposal $ ps) unChangedPropsL getProposal
        addActiveProposal ps

    deactivateProposal id = RollT $ do
        insertIfNotExist id unChangedPropsL getProposal
        deactivateProposal id

    setEpochProposers proposers = RollT $ do
        whenNothingM_ (use unPrevProposersL) $ do
            prev <- getEpochProposers
            unPrevProposersL .= Just prev
        setEpochProposers proposers

insertIfNotExist
    :: (Eq a, Hashable a, MonadState USUndo m)
    => a
    -> Lens' USUndo (HashMap a (PrevValue b))
    -> (a -> m (Maybe b))
    -> m ()
insertIfNotExist id setter getter = do
    res <- HM.lookup id <$> use setter
    case res of
        Nothing -> do
            prev <- getter id
            setter %= HM.insert id (maybeToPrev prev)
        Just _  -> pass

runRollT :: RollT m a -> m (a, USUndo)
runRollT = flip runStateT def . getRollT

execRollT :: Monad m => RollT m a -> m USUndo
execRollT = flip execStateT def . getRollT
