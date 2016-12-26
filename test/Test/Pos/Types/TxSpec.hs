{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE ViewPatterns     #-}

-- | Specification for transaction-related functions
-- (Pos.Types.Tx)
module Test.Pos.Types.TxSpec
       ( spec
       ) where

import           Control.Lens           (view, _2, _3, _4)
import           Control.Monad          (join)
import qualified Data.HashMap.Strict    as HM
import           Data.List              (elemIndex, lookup, zipWith3, (\\))
import qualified Data.Map               as M (singleton)
import qualified Data.Vector            as V (fromList, singleton, toList)
import           Formatting             (build, int, sformat, shown, (%))
import           Serokell.Util.Text     (listJsonIndent)
import           Serokell.Util.Verify   (VerificationRes (..), isVerFailure, isVerSuccess)
import           Test.Hspec             (Expectation, Spec, describe, expectationFailure,
                                         it, shouldSatisfy)
import           Test.Hspec.QuickCheck  (prop)
import           Test.QuickCheck        (NonNegative (..), Positive (..), Property,
                                         arbitrary, forAll, resize, shuffle, vectorOf,
                                         (.&.), (===))
import           Test.QuickCheck.Gen    (Gen, unGen)
import           Test.QuickCheck.Random (mkQCGen)
import qualified Text.Regex.TDFA        as TDFA
import qualified Text.Regex.TDFA.Text   as TDFA
import           Universum              hiding ((.&.))
import           Unsafe                 (unsafeHead)

import           Pos.Crypto             (checkSig, hash, unsafeHash, whData, withHash)
import           Pos.Data.Attributes    (mkAttributes)
import           Pos.Script             (Script)
import           Pos.Script.Examples    (alwaysSuccessValidator, badIntRedeemer,
                                         goodIntRedeemer, goodIntRedeemerWithBlah,
                                         goodStdlibRedeemer, idValidator, intValidator,
                                         intValidatorWithBlah, stdlibValidator)
import           Pos.Types              (BadSigsTx (..), GoodTx (..), OverflowTx (..),
                                         SmallBadSigsTx (..), SmallGoodTx (..),
                                         SmallOverflowTx (..), Tx (..), TxAux,
                                         TxDistribution (..), TxIn (..), TxInWitness (..),
                                         TxOut (..), TxOutAux, TxWitness, Utxo,
                                         VTxGlobalContext (..), VTxLocalContext (..),
                                         checkPubKeyAddress, makePubKeyAddress,
                                         makeScriptAddress, topsortTxs, verifyTxAlone,
                                         verifyTxPure, verifyTxUtxoPure)
import           Pos.Util               (sublistN)


spec :: Spec
spec = describe "Types.Tx" $ do
    describe "verifyTxAlone" $ do
        prop description_validateGoodTxAlone validateGoodTxAlone
        prop description_invalidateBadTxAlone invalidateBadTxAlone
    describe "verifyTx" $ do
        prop description_validateGoodTx validateGoodTx
        prop description_overflowTx overflowTx
        prop description_badSigsTx badSigsTx
{-
    describe "topsortTxs" $ do
        prop "doesn't change the random set of transactions" $
            forAll (resize 10 $ arbitrary) $ \(NonNegative l) ->
            forAll (vectorOf l (txGen 10)) $ \txs ->
            (sort <$> topsortTxs identity (map withHash txs)) === Just (sort $ map withHash txs)
        prop "graph generator does not produce loops" $
            forAll (txAcyclicGen False 20) $ \(txs,_) ->
            forAll (shuffle $ map withHash txs) $ \shuffled ->
            isJust $ topsortTxs identity shuffled
        prop "does correct topsort on bamboo" $ testTopsort True
        prop "does correct topsort on arbitrary acyclic graph" $ testTopsort False -}
    scriptTxSpec
  where
    description_validateGoodTxAlone =
        "validates Txs with positive coins and non-empty inputs and outputs"
    description_invalidateBadTxAlone =
        "invalidates Txs with non-positive coins or empty inputs/outputs"
    description_validateGoodTx =
        "validates a transaction whose inputs and well-formed transaction outputs"
    description_overflowTx =
        "a well-formed transaction with input and output sums above maxBound :: Coin \
        \is validated successfully"
    description_badSigsTx = "a transaction with inputs improperly signed is never validated"

scriptTxSpec :: Spec
scriptTxSpec = describe "script transactions" $ do
    describe "good cases" $ do
        it "goodIntRedeemer + intValidator" $ do
            let res = checkScriptTx
                    intValidator
                    (ScriptWitness intValidator goodIntRedeemer)
            res `shouldSatisfy` isVerSuccess

        it "goodStdlibRedeemer + stdlibValidator" $ do
            let res = checkScriptTx
                    stdlibValidator
                    (ScriptWitness stdlibValidator goodStdlibRedeemer)
            res `shouldSatisfy` isVerSuccess

    describe "bad cases" $ do
        it "a P2PK tx spending a P2SH tx" $ do
            let res = checkScriptTx
                    alwaysSuccessValidator
                    randomPkWitness
            res `errorsShouldMatch` [
                "input #0's witness doesn't match address.*\
                    \address details: ScriptAddress.*\
                    \witness: PkWitness.*",
                "input #0 isn't validated by its witness.*\
                    \signature check failed.*" ]

        it "validator script provided in witness doesn't match \
           \the validator for which the address was created" $ do
            let res = checkScriptTx
                    alwaysSuccessValidator
                    (ScriptWitness intValidator goodIntRedeemer)
            res `errorsShouldMatch` [
                "input #0's witness doesn't match address.*\
                     \address details: ScriptAddress.*\
                     \witness: ScriptWitness.*" ]

        it "validator script isn't a proper validator, \
           \redeemer script isn't a proper redeemer" $ do
            let res = checkScriptTx
                    goodIntRedeemer
                    (ScriptWitness goodIntRedeemer intValidator)
            res `errorsShouldMatch` [
                "input #0 isn't validated by its witness.*\
                    \reason: The validator script is missing `validator`.*\
                    \the redeemer script is missing `redeemer`"]

        it "redeemer >>= validator doesn't typecheck" $ do
            let res = checkScriptTx
                    idValidator
                    (ScriptWitness idValidator goodIntRedeemer)
            res `errorsShouldMatch` [
                "input #0 isn't validated by its witness.*\
                    \reason: The validation result isn't of type Comp.*"]

        it "redeemer and validator define same names" $ do
            let res = checkScriptTx
                    intValidatorWithBlah
                    (ScriptWitness intValidatorWithBlah
                                   goodIntRedeemerWithBlah)
            res `errorsShouldMatch` [
                "input #0 isn't validated by its witness.*\
                    \reason: There are overlapping declared names \
                    \in these scripts: User \"blah\"*"]

        it "redeemer >>= validator outputs 'failure'" $ do
            let res = checkScriptTx
                    intValidator
                    (ScriptWitness intValidator badIntRedeemer)
            res `errorsShouldMatch` [
                "input #0 isn't validated by its witness.*\
                    \reason: result of evaluation is 'failure'.*"]

  where
    -- Some random stuff we're going to use when building transactions
    randomPkOutput = runGen $ do
        key <- arbitrary
        return (TxOut (makePubKeyAddress key) 1)
    randomPkWitness = runGen $
        PkWitness <$> arbitrary <*> arbitrary
    -- Make utxo with a single output; return utxo, the output, and an
    -- input that can be used to spend that output
    mkUtxo :: TxOut -> (TxIn, TxOut, Utxo)
    mkUtxo outp =
        let txid = unsafeHash ("nonexistent tx" :: Text)
        in  (TxIn txid 0, outp, M.singleton (txid, 0) (outp, []))
    -- Try to apply a transaction (with given utxo as context) and say
    -- whether it applied successfully
    tryApplyTx :: Utxo -> TxAux -> VerificationRes
    tryApplyTx utxo txa = verifyTxUtxoPure True utxo txa

    -- Test tx1 against tx0. Tx0 will be a script transaction with given
    -- validator. Tx1 will be a P2PK transaction spending tx0 (with given
    -- input witness).
    checkScriptTx :: Script -> TxInWitness -> VerificationRes
    checkScriptTx val wit =
        let (inp, _, utxo) = mkUtxo $
                TxOut (makeScriptAddress val) 1
            tx = Tx [inp] [randomPkOutput] (mkAttributes ())
        in tryApplyTx utxo (tx, V.singleton wit, TxDistribution [[]])

-- | Test that errors in a 'VerFailure' match given regexes.
errorsShouldMatch :: VerificationRes -> [Text] -> Expectation
errorsShouldMatch VerSuccess _ =
    expectationFailure "expected to have errors, but there were none"
errorsShouldMatch (VerFailure xs) ys = do
    let lx = length xs
        ly = length ys
    when (lx /= ly) $ expectationFailure $ toString $ sformat
        ("expected "%int%" errors: "%listJsonIndent 0%"\n"%
         "but there were "%int%" errors: "%listJsonIndent 0)
        ly ys lx xs
    sequence_ $ zipWith3 tryMatch [1 :: Int ..] xs ys
  where
    tryMatch i x y = do
        let mbRegexp = TDFA.compile
                         TDFA.defaultCompOpt{TDFA.multiline = False}
                         TDFA.defaultExecOpt
                         y
        regexp <- case mbRegexp of
            Right r -> return r
            Left e -> do expectationFailure $ toString $ sformat
                             ("couldn't compile regex for #"%int%": "%build)
                             i e
                         return (panic "fail")
        unless (TDFA.matchTest regexp x) $
            expectationFailure $ toString $ sformat
                ("error #"%int%" doesn't match the regexp:\n"%
                 shown%"\n\n"%
                 build)
                i y x

-- | Get something out of a Gen without IO
runGen :: Gen a -> a
runGen g = unGen g (mkQCGen 31415926) 30

validateGoodTxAlone :: Tx -> Bool
validateGoodTxAlone tx = isVerSuccess $ verifyTxAlone tx

invalidateBadTxAlone :: Tx -> Bool
invalidateBadTxAlone Tx {..} = all (isVerFailure . verifyTxAlone) badTxs
  where
    zeroOutputs = fmap (\(TxOut a _) -> TxOut a (negate 0)) txOutputs
    badTxs =
        map (\(is, os) -> Tx is os (mkAttributes ())) $
        [([], txOutputs), (txInputs, []), (txInputs, zeroOutputs)]

type TxVerifyingTools =
    ((Tx, TxDistribution), TxIn -> Maybe TxOutAux,
     [Maybe (TxIn, TxOutAux)], TxWitness)

-- | This function takes the list inside a 'GoodTx' and related types, and
-- turns it into something 'verifyTx' can use:
--
-- * the transaction that the list holds
-- * the input resolver associated with that transaction
-- * the list of resolved inputs with all inputs in the transaction
getTxFromGoodTx
    :: [((Tx, TxDistribution), TxIn, TxOutAux, TxInWitness)]
    -> TxVerifyingTools
getTxFromGoodTx ls =
    let txWitness = V.fromList $ fmap (view _4) ls
        (txOutputs, TxDistribution -> txDist) = unzip $ map (view _3) ls
        txInputs = map (view _2) ls
        inpResolver :: TxIn -> Maybe TxOutAux
        inpResolver inp = lookup inp
            [ (i, (unsafeHead o, unsafeHead d))  -- here we rely on
                                                 -- txs having only one output
            | ((Tx _ o _, TxDistribution d), i, _, _) <- ls ]
        extendInput txIn = (txIn,) <$> inpResolver txIn
        extendedInputs :: [Maybe (TxIn, TxOutAux)]
        extendedInputs = map extendInput txInputs
        txAttributes = mkAttributes ()
    in ((Tx {..}, txDist), inpResolver, extendedInputs, txWitness)

-- | This function takes a list of resolved inputs from a transaction, that
-- same transaction's outputs, and verifies that the input sum is greater than
-- the output sum.
txChecksum :: [Maybe (TxIn, TxOutAux)] -> [TxOut] -> Bool
txChecksum extendedInputs txOuts =
    let inpSum = sum $ map (toInteger . txOutValue . fst . snd) $ catMaybes extendedInputs
        outSum = sum $ map (toInteger . txOutValue) txOuts
    in inpSum >= outSum

-- | This function, used in 'verifyGoodTx', takes a 'GoodTx' and checks that
-- each property verified by 'verifyTx' holds, meaning:
--
-- * sum of inputs ≥ sum of outputs;
-- * every input is signed properly;
-- * every input is a known unspent output.
-- It also checks that it has good structure w.r.t. 'verifyTxAlone'.
individualTxPropertyVerifier :: TxVerifyingTools -> Bool
individualTxPropertyVerifier ((tx@Tx{..}, dist), _, extendedInputs, txWits) =
    let hasGoodSum = txChecksum extendedInputs txOutputs
        hasGoodStructure = isVerSuccess $ verifyTxAlone tx
        hasGoodInputs = all
            (signatureIsValid (zip txOutputs (getTxDistribution dist)))
            (zip extendedInputs (toList txWits))
    in hasGoodSum && hasGoodStructure && hasGoodInputs

validateGoodTx :: SmallGoodTx -> Bool
validateGoodTx (SmallGoodTx (getGoodTx -> ls)) =
    let quadruple@((tx, dist), inpResolver, _, txWits) =
            getTxFromGoodTx ls
        transactionIsVerified = isRight $
            verifyTxPure True
                VTxGlobalContext
                (fmap VTxLocalContext <$> inpResolver)
                (tx, txWits, dist)
        transactionReallyIsGood = individualTxPropertyVerifier quadruple
    in  transactionIsVerified == transactionReallyIsGood

overflowTx :: SmallOverflowTx -> Bool
overflowTx (SmallOverflowTx (getOverflowTx -> ls)) =
    let ((tx@Tx{..}, dist), inpResolver, extendedInputs, txWits) =
            getTxFromGoodTx ls
        transactionIsNotVerified = isLeft $
            verifyTxPure True
                VTxGlobalContext
                (fmap VTxLocalContext <$> inpResolver)
                (tx, txWits, dist)
        inpSumLessThanOutSum = not $ txChecksum extendedInputs txOutputs
    in inpSumLessThanOutSum == transactionIsNotVerified

signatureIsValid :: [TxOutAux] -> (Maybe (TxIn, TxOutAux), TxInWitness) -> Bool
signatureIsValid outs (Just (TxIn{..}, (TxOut{..}, _)), PkWitness{..}) =
    let (txOutputs, TxDistribution -> txDist) = unzip outs in
    checkPubKeyAddress twKey txOutAddress &&
    checkSig twKey (txInHash, txInIndex, hash txOutputs, hash txDist) twSig
signatureIsValid _ _ = False

signatureIsNotValid :: [TxOutAux] -> (Maybe (TxIn, TxOutAux), TxInWitness) -> Bool
signatureIsNotValid txOutputs = not . signatureIsValid txOutputs

badSigsTx :: SmallBadSigsTx -> Bool
badSigsTx (SmallBadSigsTx (getBadSigsTx -> ls)) =
    let ((tx@Tx{..}, dist), inpResolver, extendedInputs, txWits) =
            getTxFromGoodTx ls
        transactionIsNotVerified = isLeft $
            verifyTxPure True
                VTxGlobalContext
                (fmap VTxLocalContext <$> inpResolver)
                (tx, txWits, dist)
        notAllSignaturesAreValid =
            any (signatureIsNotValid (zip txOutputs (getTxDistribution dist)))
                (zip extendedInputs (V.toList txWits))
    in notAllSignaturesAreValid == transactionIsNotVerified

{-

-- | Primitive transaction generator with restriction on
-- inputs/outputs size
txGen :: Int -> Gen Tx
txGen size = do
    (Positive inputsN) <- resize size arbitrary
    (Positive outputsN) <- resize size arbitrary
    inputs <- replicateM inputsN $ (\h -> TxIn h 0) <$> arbitrary
    outputs <- replicateM outputsN $
        (\addr (Positive c) -> TxOut addr c) <$> arbitrary <*> arbitrary
    pure $ Tx inputs outputs

testTopsort :: Bool -> Property
testTopsort isBamboo =
    forAll (txAcyclicGen isBamboo 40) $ \(txs,reach) ->
    forAll (shuffle txs) $ \shuffled ->
    let reachables :: [(Tx,Tx)]
        reachables = [(from,to) | (to,froms) <- HM.toList reach, from <- froms]
        topsorted = map whData <$> topsortTxs identity (map withHash shuffled)
        reaches :: (Tx,Tx) -> Bool
        reaches (from,to) =
            let fromI = elemIndex from =<< topsorted
                toI = elemIndex to =<< topsorted
            in Just True == ((<=) <$> fromI <*> toI)
    in isJust topsorted .&. all reaches reachables

-- | Produces acyclic oriented graph of transactions. It's
-- connected. Signatures are faked and thus fail to
-- verify. Transaction balance is bad too (input can be less than
-- output). These properties are not needed for topsort test. It also
-- returns reachability map as the second argument (for every key
-- elems from which we can reach key).
txAcyclicGen :: Bool -> Int -> Gen ([Tx], HM.HashMap Tx [Tx])
txAcyclicGen _ 0 = pure ([], HM.empty)
txAcyclicGen isBamboo size = do
    initVertices <-
        replicateM (bool (max 1 $ size `div` 4) 1 isBamboo) $ txGen some'
    let outputs =
            concatMap (\tx -> map (tx,) [0..length (txOutputs tx) - 1])
                      initVertices
        reachable = HM.fromList $ map (\v -> (v, [v])) initVertices
    continueGraph initVertices outputs reachable $ size - length initVertices
  where
    some' = bool 4 1 isBamboo
    continueGraph
        :: [Tx]
        -> [(Tx, Int)]
        -> HM.HashMap Tx [Tx]
        -> Int
        -> Gen ([Tx], HM.HashMap Tx [Tx])
    continueGraph vertices _ reachable 0 = pure (vertices, reachable)
    continueGraph vertices unusedUtxo reachable k = do
        -- how many nodes to connect to (how many utxo to use)
        (NonNegative depsN) <-
            resize (bool (min 3 $ length unusedUtxo) 1 isBamboo) arbitrary
        chosenUtxo <- sublistN depsN unusedUtxo
        -- grab some inputs
        let inputs = map (\(h,i) -> TxIn (hash h) (fromIntegral i)) chosenUtxo
        (Positive outputsN) <- resize some' arbitrary
        -- gen some outputs
        outputs <- replicateM outputsN $
            (\addr (Positive c) -> TxOut addr c) <$> arbitrary <*> arbitrary
        -- calculate new utxo & add vertex
        let tx = Tx inputs outputs
            producedUtxo = map (tx,) $ [0..(length outputs) - 1]
            newVertices = tx : vertices
            newUtxo = (unusedUtxo \\ chosenUtxo) ++ producedUtxo
            newReachableV = tx : concat (mapMaybe (\(x,_) -> HM.lookup x reachable) chosenUtxo)
            newReachable = HM.insert tx newReachableV reachable
        continueGraph newVertices newUtxo newReachable (k-1)

-}
