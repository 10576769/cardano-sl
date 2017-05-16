-- | Type stored in the Txp holder.

module Pos.Txp.MemState.Types
       ( GenericTxpLocalData (..)
       , GenericTxpLocalDataPure
       , TxpLocalData
       , TxpLocalDataPure
       , TxpMetrics (..)
       , ignoreTxpMetrics
       ) where

import           GHC.Base               (Int, IO)
import           Universum
import           Data.Time.Units        (Microsecond)

import           Pos.Core.Types     (HeaderHash)
import           Pos.Txp.Toil.Types (MemPool, UndoMap, UtxoModifier)

-- | LocalData of transactions processing.
-- There are two invariants which must hold for local data
-- (where um is UtxoModifier, memPool is MemPool and tip is HeaderHash):
-- 1. Suppose 'blks' is sequence of blocks from the very beginning up
-- to 'tip'. If one applies 'blks' to genesis Utxo, resulting Utxo
-- (let's call it 'utxo1') will be such that all transactions from
-- 'memPool' are valid with respect to it.
-- 2. If one applies all transactions from 'memPool' to 'utxo1',
-- resulting Utxo will be equivalent to 'um' with respect to
-- MonadUtxo.

-- | Memory state of Txp. Generic version.
data GenericTxpLocalData extra = TxpLocalData
    { txpUtxoModifier :: !(TVar UtxoModifier)
    , txpMemPool      :: !(TVar MemPool)
    , txpUndos        :: !(TVar UndoMap)
    , txpTip          :: !(TVar HeaderHash)
    , txpExtra        :: !(TVar extra)
    }

-- | Pure version of GenericTxpLocalData.
type GenericTxpLocalDataPure extra = (UtxoModifier, MemPool, UndoMap, HeaderHash, extra)

-- | Memory state of Txp. This version is used by actual Txp implementation.
type TxpLocalData = GenericTxpLocalData ()

-- | Pure version of TxpLocalData.
type TxpLocalDataPure = GenericTxpLocalDataPure ()

-- | Effectful setters for metrics related to the Txp data.
--   TODO this should not be fixed at IO, if being able to mock features
--   remains a goal. But we can't free it up right now because the current
--   mockable system doesn't work well with ether.
data TxpMetrics = TxpMetrics
    { -- | Called when a thread begins to wait to modify the mempool.
      txpMetricsWait :: !(IO ())
      -- | Called when a thread is granted the lock on the mempool. Parameter
      --   indicates how long it waited.
    , txpMetricsAcquire :: !(Microsecond -> IO ())
      -- | Called when a thread is finished modifying the mempool and has
      --   released the lock. Parameters indicates time elapsed since acquiring
      --   the lock, and new mempool size.
    , txpMetricsRelease :: !(Microsecond -> Int -> IO ())
    }

-- | A TxpMetrics never does any writes. Use it if you don't care about metrics.
ignoreTxpMetrics :: TxpMetrics
ignoreTxpMetrics = TxpMetrics
    { txpMetricsWait = (pure ())
    , txpMetricsAcquire = (const (pure ()))
    , txpMetricsRelease = (const (const (pure ())))
    }
