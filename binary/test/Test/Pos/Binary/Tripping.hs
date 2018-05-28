{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Pos.Binary.Tripping
       ( goldenTestBi
       , embedGoldenTest
       , runTests
       , trippingBiBuildable
       , trippingBiShow
       , compareHexDump
       ) where

import           Universum

-- import qualified Data.ByteString.Base16.Lazy as B16
import qualified Data.ByteString.Lazy.Char8 as BS
import           Data.FileEmbed (embedStringFile, makeRelativeToProject)
import           Data.Text.Buildable (Buildable (..))
import           Data.Text.Internal.Builder (fromText, toLazyText)
import qualified Data.Text.Lazy as LazyText
import           Language.Haskell.TH (ExpQ)

import           Hedgehog (MonadTest, (===))
import qualified Hedgehog as H
import           Hedgehog.Internal.Property (Diff (..), failWith)
import           Hedgehog.Internal.Show (LineDiff, lineDiff, mkValue, renderLineDiff, showPretty,
                                         valueDiff)

import           Pos.Binary.Class (Bi (..), decodeFull, serialize)

import qualified Prelude

import           Text.Show.Pretty (Value (..), parseValue)

import qualified Test.Pos.Util.Base16 as B16

runTests :: [IO Bool] -> IO ()
runTests tests = do
    result <- and <$> sequence tests
    unless result
        exitFailure

type HexDump = LByteString

type HexDumpDiff = [LineDiff]

renderHexDumpDiff :: HexDumpDiff -> String
renderHexDumpDiff = Prelude.unlines . fmap renderLineDiff

-- | Diff two @HexDump@s by comparing lines pairwise
hexDumpDiff :: HexDump -> HexDump -> Maybe HexDumpDiff
hexDumpDiff x y =
  concatMap (uncurry lineDiff)
    ... zipWithPadding (String "") (String "")
    <$> (sequence $ mkValue <$> BS.lines x)
    <*> (sequence $ mkValue <$> BS.lines y)

zipWithPadding :: a -> b -> [a] -> [b] -> [(a,b)]
zipWithPadding a b (x:xs) (y:ys) = (x,y) : zipWithPadding a b xs ys
zipWithPadding a _ []     ys     = zip (repeat a) ys
zipWithPadding _ b xs     []     = zip xs (repeat b)

-- | A custom version of @(===)@ for @HexDump@s to get prettier diffs
compareHexDump :: (MonadTest m, HasCallStack) => HexDump -> HexDump -> m ()
compareHexDump x y = do
    ok <- withFrozenCallStack $ H.eval (x == y)
    if ok then H.success else withFrozenCallStack $ failHexDumpDiff x y

-- | Fail with a nice line diff of the two HexDumps
failHexDumpDiff :: (MonadTest m, HasCallStack) => HexDump -> HexDump -> m ()
failHexDumpDiff x y =
  case hexDumpDiff x y of
    Nothing ->
      withFrozenCallStack $
        failWith Nothing $ Prelude.unlines [
            "━━━ Not Equal ━━━"
          , showPretty x
          , showPretty y
          ]
    Just diff ->
      withFrozenCallStack $ failWith Nothing $ renderHexDumpDiff diff

-- | A handy shortcut for embedding golden testing files
embedGoldenTest :: FilePath -> ExpQ
embedGoldenTest path = makeRelativeToProject ("golden/" <> path) >>= embedStringFile

-- | Round trip
goldenTestBi :: (Bi a, Eq a, Show a, HasCallStack) => a -> LByteString -> H.Property
goldenTestBi x bs = withFrozenCallStack $ do
    let bs' = B16.encodeWithIndex . serialize $ x
    let target = B16.decode bs
    H.withTests 1 . H.property $ do
        -- length bss === length bss'
        -- void . mapM (uncurry (===)) $ zip bss bss'
        compareHexDump bs bs'
        fmap decodeFull target === Just (Right x)

-- | Round trip test a value (any instance of both the 'Bi' and 'Show' classes)
-- by serializing it to a ByteString and back again and
--   that also has a 'Show' instance.
-- If the 'a' type has both 'Show' and 'Buildable' instances, its best to
-- use this version.
trippingBiShow :: (Bi a, Eq a, MonadTest m, Show a) => a -> m ()
trippingBiShow x =
    H.tripping x serialize decodeFull

-- | Round trip (via ByteString) any instance of the 'Bi' class
-- that also has a 'Buildable' instance.
trippingBiBuildable :: (Bi a, Buildable a, Eq a, MonadTest m) => a -> m ()
trippingBiBuildable x =
  let mx = pure x
      i = serialize x
      my = decodeFull i
  in if mx == my
        then H.success
        else case valueDiff <$> buildValue mx <*> buildValue my of
            Nothing ->
                withFrozenCallStack $
                    failWith Nothing $ Prelude.unlines
                        [ "━━━ Original ━━━"
                        , buildPretty mx
                        , "━━━ Intermediate ━━━"
                        , BS.unpack i
                        , "━━━ Roundtrip ━━━"
                        , buildPretty my
                        ]

            Just diff ->
                withFrozenCallStack $
                    failWith
                        (Just $ Diff "━━━ " "- Original" "/" "+ Roundtrip" " ━━━" diff) $
                            Prelude.unlines
                            [ "━━━ Intermediate ━━━"
                            , BS.unpack i
                            ]


instance Buildable a => Buildable (Either Text a) where
    build (Left t)  = fromText t
    build (Right a) = build a

buildPretty :: Buildable a => a -> String
buildPretty = show . buildValue

buildValue :: Buildable a => a -> Maybe Value
buildValue = parseValue . stringBuild

stringBuild :: Buildable a => a -> String
stringBuild =
    LazyText.unpack . toLazyText  . build
