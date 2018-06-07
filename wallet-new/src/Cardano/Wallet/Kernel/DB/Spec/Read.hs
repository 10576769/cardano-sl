-- | READ-only operations on the wallet-spec state
module Cardano.Wallet.Kernel.DB.Spec.Read (
    -- * Reads
    accountTotalBalance
  , accountUtxo
  ) where

import           Universum

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Pos.Core as Core
import           Pos.Core.Txp (TxOut (..), TxOutAux (..))
import           Pos.Txp (Utxo)

import           Cardano.Wallet.Kernel.DB.InDb
import           Cardano.Wallet.Kernel.DB.Spec
import           Cardano.Wallet.Kernel.DB.Spec.Util

{-------------------------------------------------------------------------------
  An address is considered "ours" if it belongs to the set of "our" addresses.
  The following pure functions are given the set of "our" addresses to enable filtering.
-------------------------------------------------------------------------------}

ourAddr :: Set Core.Address -> Core.Address -> Bool
ourAddr addrs addr = Set.member addr addrs

-- | Determines whether the transaction output address is one of "ours"
ourTxOut :: Set Core.Address -> TxOutAux -> Bool
ourTxOut addrs tx
    = ourAddr addrs (txOutAddress . toaOut $ tx)

-- | Filters the given utxo by selecting only utxo outputs that are "ours"
ourUtxo :: Set Core.Address -> Utxo -> Utxo
ourUtxo addrs utxo
    = Map.filter (ourTxOut addrs) utxo

{-------------------------------------------------------------------------------
  Pure functions that support read-only operations on an account Checkpoint, as
  defined in the Wallet Spec
-------------------------------------------------------------------------------}

accountUtxo :: Checkpoint -> Utxo
accountUtxo = view (checkpointUtxo . fromDb)

accountUtxoBalance :: Checkpoint -> Core.Coin
accountUtxoBalance = view (checkpointUtxoBalance . fromDb)

accountPendingTxs :: Checkpoint -> PendingTxs
accountPendingTxs = view (checkpointPending . pendingTransactions . fromDb)

-- | The Available Balance is the cached utxo balance minus any (pending) spent utxo
accountAvailableBalance :: Checkpoint -> Core.Coin
accountAvailableBalance c =
    fromMaybe subCoinErr balance'
    where
        subCoinErr = error "Coin arithmetic error: subCoin utxoBalance balanceDelta"

        pendingIns = txIns (accountPendingTxs c)
        spentUtxo  = utxoRestrictToInputs (accountUtxo c) pendingIns

        balance' = Core.subCoin (accountUtxoBalance c) (balance spentUtxo)

-- | Account Change refers to any pending outputs paid back into the
--   account (represented by the given checkpoint).
--
-- NOTE: computing 'change' requires filtering "our" addresses
accountChange :: (Utxo -> Utxo) -> Checkpoint -> Utxo
accountChange ours
    = ours . pendingUtxo . accountPendingTxs

-- | The Account Total Balance is the 'available' balance plus any 'change'
--
-- NOTE: computing 'total balance' requires filtering "our" addresses, which requires
--       the full set of addresses for this Account Checkpoint
accountTotalBalance :: Set Core.Address -> Checkpoint -> Core.Coin
accountTotalBalance addrs c
    = add' availableBalance changeBalance
    where
        add' = Core.unsafeAddCoin
        ourUtxo' = ourUtxo addrs

        availableBalance = accountAvailableBalance c
        changeBalance    = balance (accountChange ourUtxo' c)
