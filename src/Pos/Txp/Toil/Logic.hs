{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies    #-}

-- | All logic of Txp,
-- it operates in terms of MonadUtxo, MonadBalances and MonadTxPool.

module Pos.Txp.Toil.Logic
       ( verifyTxp
       , applyTxp
       , rollbackTxp
       , normalizeTxp
       , processTx
       ) where

import           Control.Monad.Except (MonadError (..))
import qualified Data.HashMap.Strict  as HM
import qualified Data.HashSet         as HS
import qualified Data.List.NonEmpty   as NE
import           Formatting           (build, sformat, (%))
import           System.Wlog          (WithLogger, logInfo)
import           Universum

import           Pos.Constants        (maxLocalTxs)
import           Pos.Core.Coin        (coinToInteger, sumCoins, unsafeAddCoin,
                                       unsafeIntegerToCoin, unsafeSubCoin)
import           Pos.Crypto           (WithHash (..), hash)
import           Pos.Types            (Coin, StakeholderId, mkCoin)

import           Pos.Txp.Core         (Tx (..), TxAux, TxId, TxUndo, TxpUndo,
                                       getTxDistribution, topsortTxs, txOutStake)
import           Pos.Txp.Toil.Class   (MonadBalances (..), MonadBalancesRead (..),
                                       MonadTxPool (..), MonadUtxo (..))
import           Pos.Txp.Toil.Failure (TxpVerFailure (..))
import qualified Pos.Txp.Toil.Utxo    as Utxo
#ifdef WITH_EXPLORER
import           Pos.Txp.Toil.Class   (MonadTxExtra (..))
import           Pos.Types            (TxExtra (..), HeaderHash)
#endif

type GlobalTxpMode m = ( MonadUtxo m
                       , MonadBalances m
                       , MonadError TxpVerFailure m
#ifdef WITH_EXPLORER
                       , MonadTxExtra m
#endif
                       , WithLogger m)

type LocalTxpMode m = ( MonadUtxo m
                      , MonadTxPool m
#ifdef WITH_EXPLORER
                      , MonadTxExtra m
#endif
                      , MonadError TxpVerFailure m)

-- CHECK: @verifyTxp
-- | Verify transactions correctness with respect to Utxo applying
-- them one-by-one.
-- Note: transactions must be topsorted to pass check.
-- Warning: this function may apply some transactions and fail
-- eventually. Use it only on temporary data.
verifyTxp :: GlobalTxpMode m => [TxAux] -> m TxpUndo
verifyTxp = mapM (processTxWithPureChecks True . withTxId)

-- | Apply transactions from one block.
applyTxp
    :: GlobalTxpMode m
    => [(TxAux, TxUndo)]
#ifdef WITH_EXPLORER
    -> HeaderHash
#endif
    -> m ()
#ifdef WITH_EXPLORER
applyTxp txun hh = do
#else
applyTxp txun = do
#endif
    let (txOutPlus, txInMinus) = concatStakes txun
    recomputeStakes txOutPlus txInMinus
#ifdef WITH_EXPLORER
    mapM_ applier $ zip [0..] txun
  where
    applier (i, (txaux@(tx, _, _), txundo)) = do
        let id = hash tx
            extra = TxExtra (Just (hh, i)) $ NE.fromList txundo
        applyTxToUtxo' (id, txaux)
        putTxExtra id extra
#else
    mapM_ (applyTxToUtxo' . withTxId . fst) txun
#endif

-- | Rollback transactions from one block.
rollbackTxp :: GlobalTxpMode m => [(TxAux, TxUndo)] -> m ()
rollbackTxp txun = do
    let (txOutMinus, txInPlus) = concatStakes txun
    recomputeStakes txInPlus txOutMinus
    mapM_ Utxo.rollbackTxUtxo $ reverse txun

-- | Get rid of invalid transactions.
-- All valid transactions will be added to mem pool and applied to utxo.
normalizeTxp
    :: LocalTxpMode m
#ifdef WITH_EXPLORER
    => [(TxId, (TxAux, TxExtra))]
#else
    => [(TxId, TxAux)]
#endif
    -> m ()
normalizeTxp txs = do
    topsorted <- note TxpCantTopsort (topsortTxs wHash txs)
    mapM_ normalize topsorted
  where
#ifdef WITH_EXPLORER
    wHash (i, ((t, _, _), _)) = WithHash t i
    normalize = runExceptT . uncurry processTx . repair
    repair (i, (txaux, extra)) = ((i, txaux), extra)
#else
    wHash (i, (t, _, _)) = WithHash t i
    normalize = runExceptT . processTx
#endif

-- CHECK: @processTx
-- #processWithPureChecks
-- Validate one transaction and also add it to mem pool and apply to utxo
-- if transaction is valid.
#ifdef WITH_EXPLORER
processTx
    :: LocalTxpMode m => (TxId, TxAux) -> TxExtra -> m ()
processTx tx@(id, aux) extra = do
#else
processTx
    :: LocalTxpMode m => (TxId, TxAux) -> m ()
processTx tx@(id, aux) = do
#endif
    whenM (hasTx id) $ throwError TxpKnown
    whenM ((>= maxLocalTxs) <$> poolSize) $ throwError TxpOverwhelmed
    undo <- processTxWithPureChecks True tx
    putTxWithUndo id aux undo
#ifdef WITH_EXPLORER
    putTxExtra id extra
#endif

----------------------------------------------------------------------------
-- Helpers
----------------------------------------------------------------------------

-- Compute new stakeholder's stakes by lists of spent and received coins.
recomputeStakes
    :: (MonadBalances m, WithLogger m)
    => [(StakeholderId, Coin)]
    -> [(StakeholderId, Coin)]
    -> m ()
recomputeStakes plusDistr minusDistr = do
    let needResolve =
            HS.toList $
            HS.fromList (map fst plusDistr) `HS.union`
            HS.fromList (map fst minusDistr)
    resolvedStakes <- mapM resolve needResolve
    totalStake <- getTotalStake
    let positiveDelta = sumCoins (map snd plusDistr)
    let negativeDelta = sumCoins (map snd minusDistr)
    let newTotalStake = unsafeIntegerToCoin $
                        coinToInteger totalStake + positiveDelta - negativeDelta

    let newStakes
          = HM.toList $
              calcNegStakes minusDistr
                  (calcPosStakes $ zip needResolve resolvedStakes ++ plusDistr)
    setTotalStake newTotalStake
    mapM_ (uncurry setStake) newStakes
  where
    createInfo = sformat ("Stake for " %build%" will be created in UtxoDB")
    resolve ad = maybe (mkCoin 0 <$ logInfo (createInfo ad)) pure =<< getStake ad
    calcPosStakes distr = foldl' plusAt HM.empty distr
    calcNegStakes distr hm = foldl' minusAt hm distr
    -- @pva701 says it's not possible to get negative coin here. We *can* in
    -- theory get overflow because we're adding and only then subtracting,
    -- but in practice it won't happen unless someone has 2^63 coins or
    -- something.
    plusAt hm (key, val) = HM.insertWith unsafeAddCoin key val hm
    minusAt hm (key, val) =
        HM.alter (maybe err (\v -> Just (unsafeSubCoin v val))) key hm
      where
        err = error ("recomputeStakes: no stake for " <> show key)

-- Concatenate stakes of the all passed transactions and undos.
concatStakes
    :: [(TxAux, TxUndo)]
    -> ([(StakeholderId, Coin)], [(StakeholderId, Coin)])
concatStakes (unzip -> (txas, undo)) = (txasTxOutDistr, undoTxInDistr)
  where
    txasTxOutDistr = concatMap concatDistr txas
    undoTxInDistr = concatMap txOutStake (concat undo)
    concatDistr (UnsafeTx {..}, _, distr) =
        concatMap txOutStake $
        toList (NE.zip _txOutputs (getTxDistribution distr))

processTxWithPureChecks
    :: (MonadUtxo m, MonadError TxpVerFailure m)
    => Bool -> (TxId, TxAux) -> m TxUndo
processTxWithPureChecks verifyVersions tx@(_, aux) = do
    undo <- Utxo.verifyTxUtxo verifyVersions aux
    applyTxToUtxo' tx
    pure undo

withTxId :: TxAux -> (TxId, TxAux)
withTxId aux@(tx, _, _) = (hash tx, aux)

applyTxToUtxo' :: MonadUtxo m => (TxId, TxAux) -> m ()
applyTxToUtxo' (i, (t, _, d)) = Utxo.applyTxToUtxo (WithHash t i) d
