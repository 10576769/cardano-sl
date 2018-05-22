-- | Common core types essential for multiple components.
module Pos.Core.Common.Types
       (
       -- * Address and StakeholderId
         AddressHash
       , AddrSpendingData (..)
       , AddrType (..)
       , Address' (..)
       , AddrAttributes (..)
       , AddrStakeDistribution (..)
       , MultiKeyDistrError (..)
       , mkMultiKeyDistr
       , Address (..)
       , addressF
       , encodeAddr
       , encodeAddrCRC32
       , decodeTextAddress

       -- * Forward-declared BlockHeader
       , BlockHeader

       -- * Stakeholders
       , StakeholderId
       , StakesMap
       , StakesList

       -- * ChainDifficulty
       , ChainDifficulty (..)

       -- * HeaderHash related types and functions
       , HeaderHash
       , headerHashF

       , SharedSeed (..)
       , SlotLeaders
       , slotLeadersF

       -- * Coin
       , Coin (..)
       , CoinPortion (..)
       , mkCoin
       , checkCoin
       , coinF
       , unsafeGetCoin
       , coinPortionDenominator
       , checkCoinPortion
       , coinPortionToDouble
       , unsafeCoinPortionFromDouble
       , maxCoinVal

       -- * Scripting
       , Script(..)
       , Script_v0
       , ScriptVersion

       -- * Newtypes
       -- ** for amounts
       , BlockCount(..)
       ) where

import           Universum

import           Codec.CBOR.Encoding (Encoding)
import           Control.Exception.Safe (Exception (displayException))
import           Control.Lens (makePrisms, _Left)
import           Control.Monad.Except (MonadError (throwError))
import           Crypto.Hash (Blake2b_224)
import           Data.Aeson (FromJSON (..), FromJSONKey (..), FromJSONKeyFunction (..), ToJSON (..),
                             ToJSONKey (..), object, withObject, (.:), (.=))
import           Data.Aeson.TH (defaultOptions, deriveJSON)
import           Data.Aeson.Types (toJSONKeyText)
import qualified Data.ByteString as BS (pack, zipWith)
import           Data.ByteString.Base58 (Alphabet (..), bitcoinAlphabet, decodeBase58, encodeBase58)
import qualified Data.ByteString.Char8 as BSC (pack)
import qualified Data.ByteString.Lazy as LBS
import           Data.Data (Data)
import           Data.Hashable (Hashable (..))
import qualified Data.Semigroup (Semigroup (..))
import qualified Data.Text.Buildable as Buildable
import           Formatting (Format, bprint, build, builder, float, int, later, sformat, (%))
import qualified PlutusCore.Program as PLCore
import           Serokell.Util (enumerate, listChunkedJson, mapJson, pairBuilder)
import           Serokell.Util.Base16 (formatBase16)
import           Serokell.Util.Base64 (JsonByteString (..))
import           System.Random (Random (..))

import           Pos.Binary.Class (Bi (..), Cons (..), Field (..), decodeCrcProtected, decodeFull',
                                   decodeListLenCanonical, decodeUnknownCborDataItem,
                                   deriveSimpleBi, deserialize, encodeCrcProtected, encodeListLen,
                                   encodeUnknownCborDataItem, enforceSize, serialize, serialize')
import           Pos.Core.Constants (sharedSeedLength)
import           Pos.Crypto.Hashing (AbstractHash, Hash, shortHashF)
import           Pos.Crypto.HD (HDAddressPayload)
import           Pos.Crypto.Signing (PublicKey, RedeemPublicKey)
import           Pos.Data.Attributes (Attributes (..), decodeAttributes, encodeAttributes)
import           Pos.Util.Util (cborError, toAesonError, toCborError)

----------------------------------------------------------------------------
-- Address, StakeholderId
----------------------------------------------------------------------------

-- | Hash used to identify address.
type AddressHash = AbstractHash Blake2b_224

-- | Stakeholder identifier (stakeholders are identified by their public keys)
type StakeholderId = AddressHash PublicKey

-- | A mapping between stakeholders and they stakes.
type StakesMap = HashMap StakeholderId Coin

-- | Stakeholders and their stakes.
type StakesList = [(StakeholderId, Coin)]

-- | Data which is bound to an address and must be revealed in order
-- to spend coins belonging to this address.
data AddrSpendingData
    = PubKeyASD !PublicKey
    -- ^ Funds can be spent by revealing a 'PublicKey' and providing a
    -- valid signature.
    | ScriptASD !Script
    -- ^ Funds can be spent by revealing a 'Script' and providing a
    -- redeemer 'Script'.
    | RedeemASD !RedeemPublicKey
    -- ^ Funds can be spent by revealing a 'RedeemPublicKey' and providing a
    -- valid signature.
    | UnknownASD !Word8 !ByteString
    -- ^ Unknown type of spending data. It consists of a tag and
    -- arbitrary 'ByteString'. It allows us to introduce a new type of
    -- spending data via softfork.
    deriving (Eq, Generic, Typeable, Show)

instance Buildable AddrSpendingData where
    build =
        \case
            PubKeyASD pk -> bprint ("PubKeyASD " %build) pk
            ScriptASD script -> bprint ("ScriptASD "%build) script
            RedeemASD rpk -> bprint ("RedeemASD "%build) rpk
            UnknownASD tag _ -> bprint ("UnknownASD with tag "%int) tag

{- NOTE: Address spending data serialization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An address is serialized as a tuple consisting of:

1. One-byte tag.
2. Data dependent on tag.

If tag is 0, 1 or 2, the type of spending data is 'PubKeyASD',
'ScriptASD' or 'RedeemASD' respectively.

If tag is greater than 2, the data is decoded as a plain 'ByteString'.

This lets us have backwards compatibility. For instance, if a newer
version of CSL adds a new type of spending data with tag 3, then older
versions would deserialize it as follows:

    UnknownASD 3 <some bytes>
-}

-- Helper function to avoid writing `:: Word8`.
w8 :: Word8 -> Word8
w8 = identity
{-# INLINE w8 #-}

instance Bi AddrSpendingData where
    encode =
        \case
            PubKeyASD pk -> encode (w8 0, pk)
            ScriptASD script -> encode (w8 1, script)
            RedeemASD redeemPK -> encode (w8 2, redeemPK)
            UnknownASD tag payload ->
                -- `encodeListLen 2` is semantically equivalent to encode (x,y)
                -- but we need to "unroll" it in order to apply CBOR's tag 24 to `payload`.
                encodeListLen 2
                    <> encode tag
                    <> encodeUnknownCborDataItem (LBS.fromStrict payload)
    decode = do
        enforceSize "AddrSpendingData" 2
        decode @Word8 >>= \case
            0 -> PubKeyASD <$> decode
            1 -> ScriptASD <$> decode
            2 -> RedeemASD <$> decode
            tag -> UnknownASD tag <$> decodeUnknownCborDataItem

-- | Type of an address. It corresponds to constructors of
-- 'AddrSpendingData'. It's separated, because 'Address' doesn't store
-- 'AddrSpendingData', but we want to know its type.
data AddrType
    = ATPubKey
    | ATScript
    | ATRedeem
    | ATUnknown !Word8
    deriving (Eq, Ord, Generic, Typeable, Show)

instance Bi AddrType where
    encode =
        encode @Word8 . \case
            ATPubKey -> 0
            ATScript -> 1
            ATRedeem -> 2
            ATUnknown tag -> tag
    decode =
        decode @Word8 <&> \case
            0 -> ATPubKey
            1 -> ATScript
            2 -> ATRedeem
            tag -> ATUnknown tag

-- | Stake distribution associated with an address.
data AddrStakeDistribution
    = BootstrapEraDistr
    -- ^ Stake distribution for bootstrap era.
    | SingleKeyDistr !StakeholderId
    -- ^ Stake distribution stating that all stake should go to the given stakeholder.
    | UnsafeMultiKeyDistr !(Map StakeholderId CoinPortion)
    -- ^ Stake distribution which gives stake to multiple
    -- stakeholders. 'CoinPortion' is a portion of an output (output
    -- has a value, portion of this value is stake). The constructor
    -- is unsafe because there are some predicates which must hold:
    --
    -- • the sum of portions must be @maxBound@ (basically 1);
    -- • all portions must be positive;
    -- • there must be at least 2 items, because if there is only one item,
    -- 'SingleKeyDistr' can be used instead (which is smaller).
    deriving (Eq, Ord, Show, Generic, Typeable)

instance Buildable AddrStakeDistribution where
    build =
        \case
            BootstrapEraDistr -> "Bootstrap era distribution"
            SingleKeyDistr id ->
                bprint ("Single key distribution ("%shortHashF%")") id
            UnsafeMultiKeyDistr distr ->
                bprint ("Multi key distribution: "%mapJson) distr

instance Bi AddrStakeDistribution where
    encode =
        \case
            BootstrapEraDistr -> encodeListLen 0
            SingleKeyDistr id -> encode (w8 0, id)
            UnsafeMultiKeyDistr distr -> encode (w8 1, distr)
    decode =
        decodeListLenCanonical >>= \case
            0 -> pure BootstrapEraDistr
            2 ->
                decode @Word8 >>= \case
                    0 -> SingleKeyDistr <$> decode
                    1 -> toCborError . (_Left %~ toText . displayException) .
                         mkMultiKeyDistr =<< decode
                    tag -> cborError $
                        "decode @AddrStakeDistribution: unexpected tag " <>
                        pretty tag
            len -> cborError $
                "decode @AddrStakeDistribution: unexpected length " <> pretty len


data MultiKeyDistrError
    = MkdMapIsEmpty
    | MkdMapIsSingleton
    | MkdNegativePortion
    | MkdSumNot1
    deriving (Show)

instance Buildable MultiKeyDistrError where
    build = mappend "mkMultiKeyDistr: " . \case
        MkdMapIsEmpty -> "map is empty"
        MkdMapIsSingleton -> "map's size is 1, use SingleKeyDistr"
        MkdNegativePortion -> "all portions must be positive"
        MkdSumNot1 -> "distributions' sum must be equal to 1"

instance Exception MultiKeyDistrError where
    displayException = toString . pretty

-- | Safe constructor of multi-key distribution. It checks invariants
-- of this distribution and returns an error if something is violated.
mkMultiKeyDistr ::
       MonadError MultiKeyDistrError m
    => Map StakeholderId CoinPortion
    -> m AddrStakeDistribution
mkMultiKeyDistr distrMap = UnsafeMultiKeyDistr distrMap <$ check
  where
    check = do
        when (null distrMap) $ throwError MkdMapIsEmpty
        when (length distrMap == 1) $ throwError MkdMapIsSingleton
        unless (all ((> 0) . getCoinPortion) distrMap) $
            throwError MkdNegativePortion
        let distrSum = sum $ map getCoinPortion distrMap
        unless (distrSum == coinPortionDenominator) $
            throwError MkdSumNot1

-- | Additional information stored along with address. It's intended
-- to be put into 'Attributes' data type to make it extensible with
-- softfork.
data AddrAttributes = AddrAttributes
    { aaPkDerivationPath  :: !(Maybe HDAddressPayload)
    , aaStakeDistribution :: !AddrStakeDistribution
    } deriving (Eq, Ord, Show, Generic, Typeable)

instance Buildable AddrAttributes where
    build (AddrAttributes {..}) =
        bprint
            ("AddrAttributes { stake distribution: "%build%
             ", derivation path: "%builder%" }")
            aaStakeDistribution
            derivationPathBuilder
      where
        derivationPathBuilder =
            case aaPkDerivationPath of
                Nothing -> "{}"
                Just _  -> "{path is encrypted}"

{- NOTE: Address attributes serialization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

'Attributes' are conceptually a map, where keys are numbers ('Word8').

For address there are two attributes:
• 0 — stake distribution, defaults to 'BootstrapEraDistr';
• 1 — derivation path, defaults to 'Nothing'.

-}

instance Bi (Attributes AddrAttributes) where
    -- FIXME @avieth it was observed that for a 150kb block, this call to
    -- encodeAttributes allocated 3.685mb
    -- Try using serialize rather than serialize', to avoid the
    -- toStrict call.
    -- Also consider using a custom builder strategy; serialized attributes are
    -- probably small, right?
    encode attrs@(Attributes {attrData = AddrAttributes derivationPath stakeDistr}) =
        encodeAttributes listWithIndices attrs
      where
        listWithIndices :: [(Word8, AddrAttributes -> LBS.ByteString)]
        listWithIndices =
            stakeDistributionListWithIndices <> derivationPathListWithIndices
        stakeDistributionListWithIndices =
            case stakeDistr of
                BootstrapEraDistr -> []
                _                 -> [(0, serialize . aaStakeDistribution)]
        derivationPathListWithIndices =
            case derivationPath of
                Nothing -> []
                -- 'unsafeFromJust' is safe, because 'case' ensures
                -- that derivation path is 'Just'.
                Just _ ->
                    [(1, serialize . unsafeFromJust . aaPkDerivationPath)]
        unsafeFromJust =
            fromMaybe
                (error "Maybe was Nothing in Bi (Attributes AddrAttributes)")

    decode = decodeAttributes initValue go
      where
        initValue =
            AddrAttributes
            { aaPkDerivationPath = Nothing
            , aaStakeDistribution = BootstrapEraDistr
            }
        go n v acc =
            case n of
                0 -> (\distr -> Just $ acc {aaStakeDistribution = distr }    ) <$> deserialize v
                1 -> (\deriv -> Just $ acc {aaPkDerivationPath = Just deriv }) <$> deserialize v
                _ -> pure Nothing

-- | Hash of this data is stored in 'Address'. This type exists mostly
-- for internal usage.
newtype Address' = Address'
    { unAddress' :: (AddrType, AddrSpendingData, Attributes AddrAttributes)
    } deriving (Eq, Show, Generic, Typeable, Bi)
    -- TODO: We are deriving 'Bi' via 'GeneralizedNewtypeDeriving'. This is
    -- enabled in the Cabal file. It would be *very bad* if we switched to
    -- @DeriveAnyClass@ and it was derived via the 'Generic' class instead.
    --
    -- When we upgrade to GHC 8.2, we can use @DerivingStrategies@ to write:
    -- @
    -- newtype Address' = Address' { ... }
    --     deriving stock (Eq, Show, Generic, Typeable)
    --     deriving newtype (Bi)
    -- @

-- | 'Address' is where you can send coins.
data Address = Address
    { addrRoot       :: !(AddressHash Address')
    -- ^ Root of imaginary pseudo Merkle tree stored in this address.
    , addrAttributes :: !(Attributes AddrAttributes)
    -- ^ Attributes associated with this address.
    , addrType       :: !AddrType
    -- ^ The type of this address. Should correspond to
    -- 'AddrSpendingData', but it can't be checked statically, because
    -- spending data is hashed.
    } deriving (Eq, Ord, Generic, Typeable, Show)

instance NFData AddrType
instance NFData AddrSpendingData
instance NFData AddrAttributes
instance NFData AddrStakeDistribution
instance NFData Address

instance Buildable Address where
    build = Buildable.build . decodeUtf8 @Text . addrToBase58

instance Bi Address where
    encode Address{..} =
        encodeCrcProtected (addrRoot, addrAttributes, addrType)
    decode = do
        (addrRoot, addrAttributes, addrType) <- decodeCrcProtected
        let res = Address {..}
        pure res

instance Hashable Address where
    hashWithSalt s = hashWithSalt s . serialize

instance FromJSONKey Address where
    fromJSONKey = FromJSONKeyTextParser (toAesonError . decodeTextAddress)

instance ToJSONKey Address where
    toJSONKey = toJSONKeyText (sformat addressF)

instance FromJSON Address where
    parseJSON = toAesonError . decodeTextAddress <=< parseJSON

instance ToJSON Address where
    toJSON = toJSON . sformat addressF

-- Encodes the `Address` __without__ the CRC32.
-- It's important to keep this function separated from the `encode`
-- definition to avoid that `encode` would call `crc32` and
-- the latter invoke `crc32Update`, which would then try to call `encode`
-- indirectly once again, in an infinite loop.
encodeAddr :: Address -> Encoding
encodeAddr Address {..} =
    encode addrRoot <> encode addrAttributes <> encode addrType

encodeAddrCRC32 :: Address -> Encoding
encodeAddrCRC32 Address{..} = encodeCrcProtected (addrRoot, addrAttributes, addrType)

-- | Currently we gonna use Bitcoin alphabet for representing addresses in
-- base58
addrAlphabet :: Alphabet
addrAlphabet = bitcoinAlphabet

addrToBase58 :: Address -> ByteString
addrToBase58 = encodeBase58 addrAlphabet . serialize'

-- | Specialized formatter for 'Address'.
addressF :: Format r (Address -> r)
addressF = build

-- | A function which decodes base58-encoded 'Address'.
decodeTextAddress :: Text -> Either Text Address
decodeTextAddress = decodeAddress . encodeUtf8
  where
    decodeAddress :: ByteString -> Either Text Address
    decodeAddress bs = do
        let base58Err = "Invalid base58 representation of address"
        dbs <- maybeToRight base58Err $ decodeBase58 addrAlphabet bs
        decodeFull' dbs

----------------------------------------------------------------------------
-- BlockHeader (forward-declaration)
----------------------------------------------------------------------------

-- We use a data family instead of a data type solely to avoid a module
-- cycle. Grep for @data instance BlockHeader@ to find the definition.
--
-- | Forward-declaration of block headers. See the corresponding type instance
-- for the actual definition.
data family BlockHeader

----------------------------------------------------------------------------
-- HeaderHash
----------------------------------------------------------------------------

-- | 'Hash' of block header.
type HeaderHash = Hash BlockHeader

-- | Specialized formatter for 'HeaderHash'.
headerHashF :: Format r (HeaderHash -> r)
headerHashF = build

----------------------------------------------------------------------------
-- Coin
----------------------------------------------------------------------------

-- | Coin is the least possible unit of currency.
newtype Coin = Coin
    { getCoin :: Word64
    } deriving (Show, Ord, Eq, Generic, Hashable, Data, NFData)

instance Buildable Coin where
    build (Coin n) = bprint (int%" coin(s)") n

instance Bounded Coin where
    minBound = Coin 0
    maxBound = Coin maxCoinVal

instance FromJSON Coin where
    parseJSON v = mkCoin <$> parseJSON v

instance ToJSON Coin where
    toJSON = toJSON . unsafeGetCoin

-- number of total coins is 45*10^9 * 10^6
--
--  Input                        | Bits to represent |
-- ------------------------------| ----------------- |
-- 0-9                           |      8 bits       |
-- 0-99                          |      16 bits      |
-- 0-999                         |      24 bits      |
-- 0-9999                        |      24 bits      |
-- 0-99999                       |      40 bits      |
-- 0-999999                      |      40 bits      |
-- 45*10^15                      |      72 bits      |
-- 45*10^9                       |      72 bits      |
-- 45*10^9 * 10^6 (maxbound)     |      72 bits      |
-- maxbound - 1                  |      72 bits      |

instance Bi Coin where
    encode = encode . unsafeGetCoin
    decode = Coin <$> decode

-- | Maximal possible value of 'Coin'.
maxCoinVal :: Word64
maxCoinVal = 45000000000000000

-- | Makes a 'Coin' but is _|_ if that coin exceeds 'maxCoinVal'.
-- You can also use 'checkCoin' to do that check.
mkCoin :: Word64 -> Coin
mkCoin c = either error (const coin) (checkCoin coin)
  where
    coin = (Coin c)
{-# INLINE mkCoin #-}

checkCoin :: MonadError Text m => Coin -> m ()
checkCoin (Coin c)
    | c <= maxCoinVal = pure ()
    | otherwise       = throwError $ "Coin: " <> show c <> " is too large"

-- | Coin formatter which restricts type.
coinF :: Format r (Coin -> r)
coinF = build

-- | Unwraps 'Coin'. It's called “unsafe” so that people wouldn't use it
-- willy-nilly if they want to sum coins or something. It's actually safe.
unsafeGetCoin :: Coin -> Word64
unsafeGetCoin = getCoin
{-# INLINE unsafeGetCoin #-}

-- | CoinPortion is some portion of Coin; it is interpreted as a fraction
-- with denominator of 'coinPortionDenominator'. The numerator must be in the
-- interval of [0, coinPortionDenominator].
--
-- Usually 'CoinPortion' is used to determine some threshold expressed as
-- portion of total stake.
--
-- To multiply a coin portion by 'Coin', use 'applyCoinPortionDown' (when
-- calculating number of coins) or 'applyCoinPortionUp' (when calculating a
-- threshold).
newtype CoinPortion = CoinPortion
    { getCoinPortion :: Word64
    } deriving (Show, Ord, Eq, Generic, Typeable, NFData, Hashable)

instance Bi CoinPortion where
    encode = encode . getCoinPortion
    decode = CoinPortion <$> decode

-- | Denominator used by 'CoinPortion'.
coinPortionDenominator :: Word64
coinPortionDenominator = (10 :: Word64) ^ (15 :: Word64)

instance Bounded CoinPortion where
    minBound = CoinPortion 0
    maxBound = CoinPortion coinPortionDenominator

-- | Make 'CoinPortion' from 'Word64' checking whether it is not greater
-- than 'coinPortionDenominator'.
checkCoinPortion
    :: MonadError Text m
    => CoinPortion -> m ()
checkCoinPortion (CoinPortion x)
    | x <= coinPortionDenominator = pure ()
    | otherwise = throwError err
  where
    err =
        sformat
            ("CoinPortion: value is greater than coinPortionDenominator: "
            %int) x

-- | Make CoinPortion from Double. Caller must ensure that value is in
-- [0..1]. Internally 'CoinPortion' stores 'Word64' which is divided by
-- 'coinPortionDenominator' to get actual value. So some rounding may take
-- place.
unsafeCoinPortionFromDouble :: Double -> CoinPortion
unsafeCoinPortionFromDouble x
    | 0 <= x && x <= 1 = CoinPortion v
    | otherwise = error "unsafeCoinPortionFromDouble: double not in [0, 1]"
  where
    v = round $ realToFrac coinPortionDenominator * x
{-# INLINE unsafeCoinPortionFromDouble #-}

coinPortionToDouble :: CoinPortion -> Double
coinPortionToDouble (getCoinPortion -> x) =
    realToFrac @_ @Double x / realToFrac coinPortionDenominator
{-# INLINE coinPortionToDouble #-}

instance Buildable CoinPortion where
    build cp@(getCoinPortion -> x) =
        bprint
            (int%"/"%int%" (approx. "%float%")")
            x
            coinPortionDenominator
            (coinPortionToDouble cp)

instance FromJSON CoinPortion where
    parseJSON v = unsafeCoinPortionFromDouble <$> parseJSON v

instance ToJSON CoinPortion where
    toJSON = toJSON . coinPortionToDouble

----------------------------------------------------------------------------
-- Script
----------------------------------------------------------------------------

-- | Version of script
type ScriptVersion = Word16

-- | A script for inclusion into a transaction.
data Script = Script
    { scrVersion :: ScriptVersion -- ^ Version
    , scrScript  :: ByteString   -- ^ Serialized script
    } deriving (Eq, Show, Generic, Typeable)

instance NFData Script
instance Hashable Script

instance Buildable Script where
    build Script{..} = bprint ("<script v"%int%">") scrVersion

instance ToJSON Script where
    toJSON Script{..} = object [
        "version"    .= scrVersion,
        "script" .= JsonByteString scrScript ]

instance FromJSON Script where
    parseJSON = withObject "Script" $ \obj -> do
        scrVersion <- obj .: "version"
        scrScript  <- getJsonByteString <$> obj .: "script"
        pure $ Script {..}

deriveSimpleBi ''Script [
    Cons 'Script [
        Field [| scrVersion :: ScriptVersion |],
        Field [| scrScript  :: ByteString   |]
    ]]

-- | Deserialized script (i.e. an AST), version 0.
type Script_v0 = PLCore.Program

----------------------------------------------------------------------------
-- SSC. It means shared seed computation, btw
----------------------------------------------------------------------------

-- | This is a shared seed used for follow-the-satoshi. This seed is
-- randomly generated by each party and eventually they agree on the
-- same value.
newtype SharedSeed = SharedSeed
    { getSharedSeed :: ByteString
    } deriving (Show, Eq, Ord, Generic, NFData, Typeable)

instance Buildable SharedSeed where
    build = formatBase16 . getSharedSeed

instance Semigroup SharedSeed where
    (<>) (SharedSeed a) (SharedSeed b) =
        SharedSeed $ BS.pack (BS.zipWith xor a b) -- fast due to rewrite rules

instance Monoid SharedSeed where
    mempty = SharedSeed $ BSC.pack $ replicate sharedSeedLength '\NUL'
    mappend = (Data.Semigroup.<>)
    mconcat = foldl' mappend mempty

instance ToJSON SharedSeed where
    toJSON = toJSON . JsonByteString . getSharedSeed

instance FromJSON SharedSeed where
    parseJSON v = SharedSeed . getJsonByteString <$> parseJSON v

deriveSimpleBi ''SharedSeed [
    Cons 'SharedSeed [
        Field [| getSharedSeed :: ByteString |]
    ]]

-- | 'NonEmpty' list of slot leaders.
type SlotLeaders = NonEmpty StakeholderId

-- | Pretty-printer for slot leaders. Note: it takes list (not
-- 'NonEmpty' as an argument, because one can always convert @NonEmpty
-- a@ to @[a]@, but it also may be convenient to use it with a simple
-- list of slot leaders).
--
-- Example:
-- [
--    (0, 44283ce5), (1, 5f53e01e), (2, 44283ce5), (3, 1a1ff703), (4, 44283ce5), (5, 44283ce5), (6, 281e5ae9), (7, 1a1ff703)
--    (8, 1a1ff703), (9, 5f53e01e), (10, 1a1ff703), (11, 44283ce5), (12, 44283ce5), (13, 5f53e01e), (14, 5f53e01e), (15, 5f53e01e)
--    (16, 44283ce5), (17, 281e5ae9), (18, 281e5ae9), (19, 44283ce5)
-- ]
slotLeadersF :: Format r ([StakeholderId] -> r)
slotLeadersF =
    later $ bprint (listChunkedJson 8) . map pairBuilder . enumerate @Int

----------------------------------------------------------------------------
-- Newtypes
----------------------------------------------------------------------------

newtype BlockCount = BlockCount {getBlockCount :: Word64}
    deriving (Eq, Ord, Num, Real, Integral, Enum, Read, Show,
              Buildable, Generic, Typeable, NFData, Hashable, Random)

deriveJSON defaultOptions ''BlockCount

instance Bi BlockCount where
    encode = encode . getBlockCount
    decode = BlockCount <$> decode

----------------------------------------------------------------------------
-- ChainDifficulty
----------------------------------------------------------------------------

-- | Chain difficulty represents necessary effort to generate a
-- chain. In the simplest case it can be number of blocks in chain.
newtype ChainDifficulty = ChainDifficulty
    { getChainDifficulty :: BlockCount
    } deriving (Show, Eq, Ord, Num, Enum, Real, Integral, Generic, Buildable, Typeable, NFData)

deriveJSON defaultOptions ''ChainDifficulty

deriveSimpleBi ''ChainDifficulty [
    Cons 'ChainDifficulty [
        Field [| getChainDifficulty :: BlockCount |]
    ]]

----------------------------------------------------------------------------
-- Template Haskell invocations, banished to the end of the module because
-- we don't want to topsort the whole module
----------------------------------------------------------------------------

makePrisms ''Address
