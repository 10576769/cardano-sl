{-# LANGUAGE TypeFamilies #-}

-- | Type classes for Toil abstraction.
-- * MonadUtxoRead and MonadUtxo for encapsulation of Utxo storage.
-- * MonadBalancesRead and MonadBalances for encapsulation of Balances storage.
-- * MonadTxPoll for encapsulation of mem pool of local transactions.

module Pos.Txp.Toil.Class
       ( MonadUtxoRead (..)
       , MonadUtxo (..)
       , MonadBalancesRead (..)
       , MonadBalances (..)
       , MonadTxPool (..)
       ) where

import           Universum

import           Control.Lens               (at, (.=))
import           Control.Monad.Trans.Class  (MonadTrans)
import qualified Ether
import           Fmt                        ((+|), (|+))
import           Serokell.Data.Memory.Units (Byte)

import           Pos.Core                   (Coin, StakeholderId)
import           Pos.Txp.Core.Types         (TxAux, TxId, TxIn, TxOutAux, TxUndo)
import           Pos.Txp.Toil.Types         (Utxo)
import           Pos.Util.Util              (ether)

----------------------------------------------------------------------------
-- MonadUtxo
----------------------------------------------------------------------------

class Monad m => MonadUtxoRead m where
    utxoGet :: TxIn -> m (Maybe TxOutAux)
    default utxoGet :: (MonadTrans t, MonadUtxoRead m', t m' ~ m) => TxIn -> m (Maybe TxOutAux)
    utxoGet = lift . utxoGet

instance {-# OVERLAPPABLE #-}
    (MonadUtxoRead m, MonadTrans t, Monad (t m)) =>
        MonadUtxoRead (t m)

instance MonadUtxoRead ((->) Utxo) where
    utxoGet id = view (at id)

instance Monad m => MonadUtxoRead (Ether.StateT' Utxo m) where
    utxoGet id = ether $ use (at id)

class MonadUtxoRead m => MonadUtxo m where
    -- | Add an unspent output to UTXO. If it's already in the UTXO, throw
    -- an error.
    utxoPut :: TxIn -> TxOutAux -> m ()
    default utxoPut :: (MonadTrans t, MonadUtxo m', t m' ~ m) => TxIn -> TxOutAux -> m ()
    utxoPut a = lift . utxoPut a
    -- | Delete an unspent input from UTXO. If it's not in the UTXO, throw
    -- an error.
    utxoDel :: TxIn -> m ()
    default utxoDel :: (MonadTrans t, MonadUtxo m', t m' ~ m) => TxIn -> m ()
    utxoDel = lift . utxoDel

instance {-# OVERLAPPABLE #-}
  (MonadUtxo m, MonadTrans t, Monad (t m)) => MonadUtxo (t m)

instance Monad m => MonadUtxo (Ether.StateT' Utxo m) where
    utxoPut id aux = ether $ use (at id) >>= \case
        Nothing -> at id .= Just aux
        Just _  -> error ("utxoPut@(StateT Utxo): "+|id|+" is already in utxo")
    utxoDel id = ether $ use (at id) >>= \case
        Just _  -> at id .= Nothing
        Nothing -> error ("utxoDel@(StateT Utxo): "+|id|+" is not in the utxo")

----------------------------------------------------------------------------
-- MonadBalances
----------------------------------------------------------------------------

class Monad m => MonadBalancesRead m where
    getStake :: StakeholderId -> m (Maybe Coin)
    getTotalStake :: m Coin

    default getStake
        :: (MonadTrans t, MonadBalancesRead m', t m' ~ m) => StakeholderId -> m (Maybe Coin)
    getStake = lift . getStake

    default getTotalStake
        :: (MonadTrans t, MonadBalancesRead m', t m' ~ m) => m Coin
    getTotalStake = lift getTotalStake

instance {-# OVERLAPPABLE #-}
    (MonadBalancesRead m, MonadTrans t, Monad (t m)) =>
        MonadBalancesRead (t m)

class MonadBalancesRead m => MonadBalances m where
    setStake :: StakeholderId -> Coin -> m ()
    setTotalStake :: Coin -> m ()

    default setStake
        :: (MonadTrans t, MonadBalances m', t m' ~ m) => StakeholderId -> Coin -> m ()
    setStake id = lift . setStake id

    default setTotalStake
        :: (MonadTrans t, MonadBalances m', t m' ~ m) => Coin -> m ()
    setTotalStake = lift . setTotalStake

instance {-# OVERLAPPABLE #-}
    (MonadBalances m, MonadTrans t, Monad (t m)) =>
        MonadBalances (t m)

----------------------------------------------------------------------------
-- MonadTxPool
----------------------------------------------------------------------------

class Monad m => MonadTxPool m where
    -- | Check whether Tx with given identifier is stored in the pool.
    hasTx :: TxId -> m Bool
    -- | Return size of the pool's binary representation (approximate).
    poolSize :: m Byte
    -- | Put a transaction with corresponding Undo into MemPool.
    -- Transaction must not be in MemPool.
    putTxWithUndo :: TxId -> TxAux -> TxUndo -> m ()

    default hasTx
        :: (MonadTrans t, MonadTxPool m', t m' ~ m) => TxId -> m Bool
    hasTx = lift . hasTx

    default poolSize
        :: (MonadTrans t, MonadTxPool m', t m' ~ m) => m Byte
    poolSize = lift poolSize

    default putTxWithUndo
        :: (MonadTrans t, MonadTxPool m', t m' ~ m) => TxId -> TxAux -> TxUndo -> m ()
    putTxWithUndo id tx = lift . putTxWithUndo id tx

instance {-# OVERLAPPABLE #-}
    (MonadTxPool m, MonadTrans t, Monad (t m)) =>
        MonadTxPool (t m)
