-- | Specification of Pos.Types.Utxo.

module Test.Pos.Types.UtxoSpec
       ( spec
       ) where

import           Data.List.NonEmpty    (NonEmpty ((:|)))
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map              as M (Map, delete, elems, fromList, insert, keys)
import           Data.Maybe            (isJust, isNothing)
import qualified Data.Vector           as V (fromList)
import           Pos.Crypto            (hash, unsafeHash, withHash)
import           Pos.Data.Attributes   (mkAttributes)
import           Pos.Txp               (Tx (..), TxDistribution (..), TxIn (..), TxOutAux,
                                        Utxo, applyTxToUtxoPure, deleteTxIn, findTxIn,
                                        verifyTxUtxoPure)
import           Pos.Types             (GoodTx (..), SmallGoodTx (..))
import           Serokell.Util.Verify  (isVerSuccess)

import           Test.Hspec            (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Universum

spec :: Spec
spec = describe "Types.Utxo" $ do
    describe "findTxIn" $ do
        it "returns Nothing when given empty list" $
            (findTxIn myTx mempty) == Nothing
        prop description_findTxInUtxo findTxInUtxo
    describe "deleteTxIn" $ do
        prop description_deleteTxInUtxo deleteTxInUtxo
    describe "verifyTxUtxoPure" $ do
        prop description_verifyTxInUtxo verifyTxInUtxo
    describe "applyTxToUtxoPure" $ do
        prop description_applyTxToUtxoGood applyTxToUtxoGood
  where
    myTx = (TxIn myHash 0)
    myHash = unsafeHash (0 :: Int64)
    description_findTxInUtxo =
        "correctly finds the TxOut corresponding to (txHash, txIndex) when the key is in\
        \ the Utxo map, and doesn't find it otherwise"
    description_deleteTxInUtxo =
        "deleting a (txHash, txIndex) key from a Utxo map where it is present returns\
        \ the map without that key, and if it's not present it does nothing"
    description_applyTxToUtxoGood =
        "correctly removes spent outputs used as inputs in given transaction and\
        \ successfully adds this transaction's outputs to the utxo map"
    description_verifyTxInUtxo =
        "successfully verifies a transaction whose inputs are all present in the utxo\
        \ map"

findTxInUtxo :: TxIn -> TxOutAux -> Utxo -> Bool
findTxInUtxo key txO utxo =
    let utxo' = M.delete key utxo
        newUtxo = M.insert key txO utxo
    in (isJust $ findTxIn key newUtxo) && (isNothing $ findTxIn key utxo')

deleteTxInUtxo :: TxIn -> TxOutAux -> Utxo -> Bool
deleteTxInUtxo key txO utxo =
    let utxo' = M.delete key utxo
        newUtxo = M.insert key txO utxo
    in (utxo' == deleteTxIn key newUtxo) && (utxo' == deleteTxIn key utxo')

verifyTxInUtxo :: SmallGoodTx -> Bool
verifyTxInUtxo (SmallGoodTx (GoodTx ls)) =
    let txs = fmap (view _1) ls
        witness = V.fromList $ toList $ fmap (view _4) ls
        (ins, outs) = NE.unzip $ map (\(_, tIs, tOs, _) -> (tIs, tOs)) ls
        newTx = UnsafeTx ins (map fst outs) (mkAttributes ())
        newDistr = TxDistribution (map snd outs)
        utxo = foldr (\(tx, d) -> applyTxToUtxoPure (withHash tx) d) mempty txs
    in isVerSuccess $
       verifyTxUtxoPure False utxo (newTx, witness, newDistr)

applyTxToUtxoGood :: (TxIn, TxOutAux) -> M.Map TxIn TxOutAux -> NonEmpty TxOutAux -> Bool
applyTxToUtxoGood (txIn0, txOut0) txMap txOuts =
    let inpList = txIn0 :| M.keys txMap
        tx = UnsafeTx inpList (map fst txOuts) (mkAttributes ())
        txDistr = TxDistribution (map snd txOuts)
        utxoMap = M.fromList $ toList $ NE.zip inpList (txOut0 :| M.elems txMap)
        newUtxoMap = applyTxToUtxoPure (withHash tx) txDistr utxoMap
        newUtxos =
            NE.fromList $
            (zipWith TxIn (repeat (hash tx)) [0 ..]) `zip` toList txOuts
        rmvUtxo = foldr M.delete utxoMap inpList
        insNewUtxo = foldr (uncurry M.insert) rmvUtxo newUtxos
    in insNewUtxo == newUtxoMap
