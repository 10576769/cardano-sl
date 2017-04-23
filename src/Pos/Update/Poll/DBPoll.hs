{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Instance of MoandPollRead which uses DB.

module Pos.Update.Poll.DBPoll
       ( DBPoll (..)
       ) where

import           Control.Lens                (iso)
import           Control.Monad.Base          (MonadBase (..))
import           Control.Monad.Except        (MonadError)
import           Control.Monad.Fix           (MonadFix)
import           Control.Monad.Trans         (MonadTrans (lift))
import           Control.Monad.Trans.Control (ComposeSt, MonadBaseControl (..),
                                              MonadTransControl (..), StM,
                                              defaultLiftBaseWith, defaultRestoreM)
import qualified Data.HashMap.Strict         as HM
import           Mockable                    (ChannelT, Counter, Distribution, Gauge,
                                              MFunctor', Mockable (liftMockable), Promise,
                                              SharedAtomicT, SharedExclusiveT, ThreadId,
                                              liftMockableWrappedM)
import           Serokell.Util.Lens          (WrappedM (..))
import           System.Wlog                 (CanLog, HasLoggerName, WithLogger)
import           Universum

import           Pos.Context                 (WithNodeContext, lrcActionOnEpochReason)
import           Pos.DB.Class                (MonadDB)
import           Pos.Delegation.Class        (MonadDelegation)
import           Pos.Lrc.Context             (LrcContext)
import           Pos.Lrc.DB                  (getIssuersStakes, getRichmenUS)
import           Pos.Lrc.Types               (FullRichmenData)
import           Pos.Ssc.Extra               (MonadSscMem)
import           Pos.Types                   (Coin)
import qualified Pos.Update.DB               as GS
import           Pos.Update.Poll.Class       (MonadPollRead (..))
import           Pos.Util.Context            (HasContext, MonadContext (..))
import           Pos.Util.JsonLog            (MonadJL (..))

----------------------------------------------------------------------------
-- Transformer
----------------------------------------------------------------------------

newtype DBPoll m a = DBPoll
    { runDBPoll :: m a
    } deriving ( Functor
               , Applicative
               , Monad
               , MonadThrow
               , MonadCatch
               , MonadIO
               , MonadFail
               , HasLoggerName
               , MonadError e
               , WithNodeContext ssc
               , MonadJL
               , CanLog
               , MonadMask
               , MonadSscMem peka
               , MonadBase io
               , MonadDelegation
               , MonadFix
               , MonadDB
               )

instance MonadContext m => MonadContext (DBPoll m) where
    type ContextType (DBPoll m) = ContextType m

----------------------------------------------------------------------------
-- Common instances used all over the code
----------------------------------------------------------------------------

type instance ThreadId (DBPoll m) = ThreadId m
type instance Promise (DBPoll m) = Promise m
type instance SharedAtomicT (DBPoll m) = SharedAtomicT m
type instance Counter (DBPoll m) = Counter m
type instance Distribution (DBPoll m) = Distribution m
type instance SharedExclusiveT (DBPoll m) = SharedExclusiveT m
type instance Gauge (DBPoll m) = Gauge m
type instance ChannelT (DBPoll m) = ChannelT m

instance MonadTrans DBPoll where
    lift = DBPoll

instance ( Mockable d m
         , MFunctor' d (DBPoll m) m
         ) => Mockable d (DBPoll m) where
    liftMockable = liftMockableWrappedM

instance Monad m => WrappedM (DBPoll m) where
    type UnwrappedM (DBPoll m) = m
    _WrappedM = iso runDBPoll DBPoll

instance MonadTransControl DBPoll where
    type StT DBPoll a = a
    liftWith f = DBPoll $ f $ runDBPoll
    restoreT = DBPoll

instance MonadBaseControl IO m => MonadBaseControl IO (DBPoll m) where
    type StM (DBPoll m) a = ComposeSt DBPoll m a
    liftBaseWith = defaultLiftBaseWith
    restoreM     = defaultRestoreM

----------------------------------------------------------------------------
-- MonadPoll
----------------------------------------------------------------------------

instance (MonadDB m, WithLogger m, HasContext LrcContext m) =>
         MonadPollRead (DBPoll m) where
    getBVState = GS.getBVState
    getProposedBVs = GS.getProposedBVs
    getEpochProposers = GS.getEpochProposers
    getCompetingBVStates = GS.getCompetingBVStates
    getAdoptedBVFull = GS.getAdoptedBVFull
    getLastConfirmedSV = GS.getConfirmedSV
    getProposal = GS.getProposalState
    getProposalsByApp = GS.getProposalsByApp
    getConfirmedProposals = GS.getConfirmedProposals Nothing
    getEpochTotalStake e = fmap fst <$> getRichmenUS e
    getRichmanStake e id = (findStake =<<) <$> getRichmenUS e
      where
        findStake :: FullRichmenData -> Maybe Coin
        findStake = HM.lookup id . snd
    getOldProposals = GS.getOldProposals
    getDeepProposals = GS.getDeepProposals
    getBlockIssuerStake epoch id =
        lrcActionOnEpochReason epoch
            "couldn't get issuers's stakes"
            (fmap (Just . HM.lookup id) . getIssuersStakes)
    getSlottingData = GS.getSlottingData
