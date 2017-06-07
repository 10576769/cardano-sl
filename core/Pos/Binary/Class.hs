{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BinaryLiterals      #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}

#include "MachDeps.h"

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | Serialization-related types

module Pos.Binary.Class
       ( Bi (..)
       , encode
       , decodeFull
       {-
       , encode
       , decode
       , decodeOrFail
       , decodeFull
       -}

       -- * Store re-exports
       , Size(..)
       , Peek
       , Poke
       -- * Primitives for serialization
       , getWord8
       , putWord8
       , getByteString
       , putByteString
       , label

       -- * The 'StaticSize' wrapper
       , StaticSize(..)

       -- * The 'Raw' wrapper
       , Raw

       -- * Different sizes for ints
       , UnsignedVarInt(..)
       , SignedVarInt(..)
       , TinyVarInt(..)
       , FixedSizeInt(..)

       -- * Primitives for limiting serialization
       , limitGet
       , isolate64Full
       -- * Bi to SafeCopy
       , getCopyBi
       , putCopyBi
       -- * Binary serialization
       , AsBinary (..)
       , AsBinaryClass (..)
       , fromBinaryM

{-
       -- * Serialization with length
       , putWithLength
       , getWithLength
       , getWithLengthLimited
       , putSmallWithLength
       , getSmallWithLength

       -- * Other binary utils
       , getRemainingByteString
       -}
       , getAsciiString1b
       , putAsciiString1b
       , biSize

       , convertSize
       , combineSize
       ) where

import           Universum

{-
import           Data.Binary                 (Get, Put)
import qualified Data.Binary                 as Binary
import           Data.Binary.Get             (ByteOffset, getByteString,
                                              getLazyByteString,
                                              getRemainingLazyByteString, getWord8, label,
                                              runGet, runGetOrFail)
import           Data.Binary.Get.Internal    (Decoder (..), runCont)
import           Data.Binary.Put             (PutM, putByteString, putCharUtf8,
                                              putLazyByteString, putWord8, runPut,
                                              runPutM)
import           Data.Hashable               (Hashable (..))
import           Unsafe.Coerce               (unsafeCoerce)
-}

import           Control.Lens                (_Left)
import           Control.Lens.Internal.TH    (appsT, newNames, toTupleT)
import           Data.Bits                   (Bits (..), FiniteBits, countLeadingZeros,
                                              finiteBitSize)
import qualified Data.ByteString             as BS
import           Data.Char                   (isAscii)
import qualified Data.HashMap.Strict         as HM
import qualified Data.HashSet                as HS
import           Data.Reflection             (reifyNat)
import           Data.SafeCopy               (Contained, SafeCopy (..), contain, safeGet,
                                              safePut)
import qualified Data.Serialize              as Cereal (Get, Put)
import qualified Data.Set                    as S
import           Data.Store                  (Size (..))
import           Data.Store.Core             (Peek (..), PeekResult (..), Poke)
import qualified Data.Store.Core             as Store
import           Data.Store.Internal         (PeekException (..), StaticSize (..))
import qualified Data.Store.Internal         as Store
import           Data.Tagged                 (Tagged (..))
import qualified Data.Text                   as T
import qualified Data.Text.Encoding          as T
import           Data.Time.Units             (Microsecond, Millisecond)
import qualified Data.Vector                 as V
import qualified Data.Vector.Generic         as G
import qualified Data.Vector.Generic.Mutable as GM
import           Data.Word                   (Word32)
import           Foreign.Ptr                 (minusPtr, plusPtr)
import           Formatting                  (formatToString, int, (%))
import           GHC.TypeLits                (ErrorMessage (..), TypeError)
import           Language.Haskell.TH
import           Serokell.Data.Memory.Units  (Byte, fromBytes, toBytes)
import           Serokell.Data.Memory.Units  (Byte)
import           System.IO.Unsafe            (unsafePerformIO)

----------------------------------------------------------------------------
-- Bi typeclass
----------------------------------------------------------------------------

-- | Simplified definition of serializable object
-- Data.Binary.Class-alike.
--
-- Write @instance Bi SomeType where@ without any method definitions if you
-- want to use the 'Binary' instance for your type.
class Bi t where
    size :: Size t
    put :: t -> Poke ()
    get :: Peek t

--instance Serializable t => B.Binary t where
--    get = get
--    put = put

-- | Encode a value to a strict bytestring
encode :: Bi a => a -> ByteString
encode x = Store.unsafeEncodeWith (put x) (getSize x)
{-# INLINE encode #-}

getSize :: Bi a => a -> Int
getSize = Store.getSizeWith size
{-# INLINE getSize #-}

decodeFull :: Bi a => ByteString -> Either Text a
decodeFull = over _Left Store.peekExMessage . Store.decodeWith get

label :: Text -> Peek a -> Peek a
label = undefined -- CSL-1122 implement

----------------------------------------------------------------------------
-- Raw
----------------------------------------------------------------------------

-- | A wrapper over 'ByteString' for adding type safety to
-- 'Pos.Crypto.Pki.encryptRaw' and friends.
--
-- TODO: maybe it should be in "Pos.Crypto"?
newtype Raw = Raw ByteString
    deriving (Bi, Eq, Ord, Show, Typeable, NFData)

----------------------------------------------------------------------------
-- Variable-sized numbers
----------------------------------------------------------------------------

-- Copied from Edward Kmett's 'bytes' library (licensed under BSD3)
putUnsignedVarInt :: (Integral a, Bits a) => a -> Poke ()
putUnsignedVarInt n
    | n < 0x80 = putWord8 $ fromIntegral n
    | otherwise = do
          putWord8 $ setBit (fromIntegral n) 7
          putUnsignedVarInt $ shiftR n 7
{-# INLINE putUnsignedVarInt #-}

getUnsignedVarIntSize :: (Integral a, Bits a, FiniteBits a) => a -> Int
getUnsignedVarIntSize n = (logBase2 n `div` 7) + 1
  where
    logBase2 x = finiteBitSize x - 1 - countLeadingZeros x
{-# INLINE getUnsignedVarIntSize #-}

getUnsignedVarInt' :: (Integral a, Bits a, FiniteBits a) => Peek a
getUnsignedVarInt' = do
    (bytes, i) <- getWord8 >>= go
    let iBytes = Store.unsafeEncodeWith (putUnsignedVarInt i) (getUnsignedVarIntSize i)
    if BS.pack bytes /= iBytes
       then fail $ "Ambigious varInt bytes: " ++ show bytes
       else return i
  where
    go n | testBit n 7 = do
             (bs, m) <- getWord8 >>= go
             return (n:bs, shiftL m 7 .|. clearBit (fromIntegral n) 7)
         | otherwise = return ([n], fromIntegral n)
{-# INLINE getUnsignedVarInt' #-}

putSignedVarInt :: (ZZEncode a b, Integral b, Bits b) => a -> Poke ()
putSignedVarInt x = putUnsignedVarInt (zzEncode x)
{-# INLINE putSignedVarInt #-}

getSignedVarInt' :: (ZZEncode a b, Integral b, Bits b, FiniteBits b) => Peek a
getSignedVarInt' = zzDecode <$> getUnsignedVarInt'
{-# INLINE getSignedVarInt' #-}

getSignedVarIntSize :: (ZZEncode a b, Integral b, Bits b, FiniteBits b) => a -> Int
getSignedVarIntSize = getUnsignedVarIntSize . zzEncode
{-# INLINE getSignedVarIntSize #-}

getTinyVarIntSize :: Word16 -> Int
getTinyVarIntSize n
    | n <= 0b1111111 = 1
    | n <= 0b11111111111111 = 2
    | otherwise =
          error "putTinyVarIntSize: the number is bigger than 2^14-1"

putTinyVarInt :: Word16 -> Poke ()
putTinyVarInt n
    | n <= 0b1111111 =
          putWord8 (fromIntegral n)
    | n <= 0b11111111111111 =
          putWord8 (setBit (fromIntegral n) 7) *>
          putWord8 (fromIntegral (shiftR n 7))
    | otherwise =
          error "putTinyVarInt: the number is bigger than 2^14-1"

getTinyVarInt' :: Peek Word16
getTinyVarInt' = do
    a <- getWord8
    if testBit a 7
        then do
            b <- getWord8
            if | testBit b 7 -> fail "getTinyVarInt': more than 2 bytes"
               | b == 0      -> fail "getTinyVarInt': second byte is 0"
               | otherwise   -> pure $ shiftL (fromIntegral b) 7 .|.
                                       clearBit (fromIntegral a) 7
        else pure (fromIntegral a)

-- | Turn a signed number into an unsigned one, and back.
--
-- >>> map zzEncode [-3, 3]
-- [5, 6]
-- >>> map zzDecode [5, 6]
-- [-3, 3]
class ZZEncode a b | a -> b, b -> a where
    zzEncode :: a -> b
    zzDecode :: b -> a

-- Copied from the 'protobuf' library (licensed under BSD3)
instance ZZEncode Int32 Word32 where
    zzEncode x = fromIntegral ((x `shiftL` 1) `xor` x `shiftR` 31)
    {-# INLINE zzEncode #-}
    zzDecode x = fromIntegral (x `shiftR` 1) `xor`
                     negate (fromIntegral (x .&. 1))
    {-# INLINE zzDecode #-}

instance ZZEncode Int64 Word64 where
    zzEncode x = fromIntegral ((x `shiftL` 1) `xor` x `shiftR` 63)
    {-# INLINE zzEncode #-}
    zzDecode x = fromIntegral (x `shiftR` 1) `xor`
                     negate (fromIntegral (x .&. 1))
    {-# INLINE zzDecode #-}

instance ZZEncode Int Word where
#if (WORD_SIZE_IN_BITS == 32)
    zzEncode x = fromIntegral ((x `shiftL` 1) `xor` x `shiftR` 31)
#elif (WORD_SIZE_IN_BITS == 64)
    zzEncode x = fromIntegral ((x `shiftL` 1) `xor` x `shiftR` 63)
    {-# INLINE zzEncode #-}
#else
# error Unsupported platform
#endif
    zzDecode x = fromIntegral (x `shiftR` 1) `xor`
                     negate (fromIntegral (x .&. 1))
    {-# INLINE zzDecode #-}

----------------------------------------------------------------------------
-- Int/Word encoding
----------------------------------------------------------------------------

-- | A newtype wrapper for non-negative varints. During serialization its
-- contents will be encoded as a variable-sized integer.
--
-- Despite its name, e.g. @UnsignedVarInt (-50 :: Int)@ will be serialized
-- and deserialized correctly; however, 'UnsignedVarInt' is optimized for
-- non-negative numbers, and will always take maximum space (e.g. 10 bytes in
-- case of 'Int64'). Specifically, @Int@ is simply coerced into its @Word@
-- representation before being serialized.
newtype UnsignedVarInt a = UnsignedVarInt {getUnsignedVarInt :: a}
    deriving (Eq, Ord, Show, Generic, NFData, Functor)

-- | A newtype wrapper for varints. Uses zig-zag encoding to serialize
-- negative integers – e.g. @-3@ is turned into 5, @-4@ is turned into 7,
-- etc; thus it's fair but less optimal for positive integers.
newtype SignedVarInt a = SignedVarInt {getSignedVarInt :: a}
    deriving (Eq, Ord, Show, Generic, NFData, Functor)

-- | A newtype wrapper for non-negative integers less than @2^14@. Use it if
-- you want to be extra careful. Compared to 'SignedVarInt' and
-- 'UnsignedVarInt', it provides two benefits:
--
-- * It is guaranteed to take either 1 or 2 bytes (the standard decoder for
--   varints can consume an unlimited amount of bytes).
--
-- * It is unambiguous (e.g. @0@ can be encoded in only one way instead of
--   two).
newtype TinyVarInt = TinyVarInt {getTinyVarInt :: Word16}
    deriving (Eq, Ord, Show, Generic, NFData)

-- | A newtype wrapper for signifying that an integer should be serialized
-- using a fixed amount of bytes.
newtype FixedSizeInt a = FixedSizeInt {getFixedSizeInt :: a}
    deriving (Eq, Ord, Show, Generic, NFData, Functor)

instance TypeError
    ('Text "Do not encode 'Int' directly. Instead, use one of newtype wrappers:" ':$$:
     'Text "  'FixedSizeInt': always uses 8 bytes" ':$$:
     'Text "  'SignedVarInt': uses 1–10 bytes (1 byte for −64..63)" ':$$:
     'Text "  'UnsignedVarInt': uses 1–10 bytes (1 byte for 0..127);" ':$$:
     'Text "                    more efficient for non-negative numbers," ':$$:
     'Text "                    but takes 10 bytes for negative numbers")
  => Bi Int
  where
    get = error "get@Int"
    put = error "put@Int"
    size = error "size@Int"

instance TypeError
    ('Text "Do not encode 'Word' directly. Instead, use one of newtype wrappers:" ':$$:
     'Text "  'FixedSizeInt': always uses 8 bytes" ':$$:
     'Text "  'UnsignedVarInt': uses 1–10 bytes (1 byte for 0..127)")
  => Bi Word
  where
    get = error "get@Word"
    put = error "put@Word"
    size = error "size@Word"

-- Int

instance Bi (UnsignedVarInt Int) where
    put (UnsignedVarInt a) = putUnsignedVarInt (fromIntegral a :: Word)
    {-# INLINE put #-}
    get = label "UnsignedVarInt Int" $
        UnsignedVarInt . (fromIntegral :: Word -> Int) <$>
        limitGet 15 getUnsignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ \(UnsignedVarInt a) ->
              getUnsignedVarIntSize (fromIntegral a :: Word)
    {-# INLINE size #-}

instance Bi (SignedVarInt Int) where
    put (SignedVarInt a) = putSignedVarInt a
    {-# INLINE put #-}
    get = label "SignedVarInt Int" $
        SignedVarInt <$> limitGet 15 getSignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ getSignedVarIntSize . getSignedVarInt
    {-# INLINE size #-}


-- Is this instance valid at all? Is it int32 or int64 after all?
instance Bi (FixedSizeInt Int) where
    put (FixedSizeInt a) = Store.poke a -- CSL-1122 fix endianess
    {-# INLINE put #-}
    get = label "FixedSizeInt Int" $
        FixedSizeInt <$> Store.peek -- CSL-1122 fix endianess
    {-# INLINE get #-}
    size = convertSize getFixedSizeInt Store.size
    {-# INLINE size #-}

-- Int64

instance Bi (UnsignedVarInt Int64) where
    put (UnsignedVarInt a) = putUnsignedVarInt (fromIntegral a :: Word64)
    {-# INLINE put #-}
    get = label "UnsignedVarInt Int64" $
        UnsignedVarInt . (fromIntegral :: Word64 -> Int64) <$>
        limitGet 15 getUnsignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ \(UnsignedVarInt a) ->
              getUnsignedVarIntSize (fromIntegral a :: Word64)
    {-# INLINE size #-}

instance Bi (SignedVarInt Int64) where
    put (SignedVarInt a) = putSignedVarInt a
    {-# INLINE put #-}
    get = label "SignedVarInt Int64" $
        SignedVarInt <$> limitGet 15 getSignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ getSignedVarIntSize . getSignedVarInt
    {-# INLINE size #-}

instance Bi (FixedSizeInt Int64) where
    put (FixedSizeInt a) = Store.poke a -- CSL-1122 fix endianess
    {-# INLINE put #-}
    get = label "FixedSizeInt Int64" $
        FixedSizeInt <$> Store.peek -- CSL-1122 fix endianess
    {-# INLINE get #-}
    size = convertSize getFixedSizeInt Store.size
    {-# INLINE size #-}

-- Word

instance Bi (UnsignedVarInt Word) where
    put (UnsignedVarInt a) = putUnsignedVarInt a
    {-# INLINE put #-}
    get = label "UnsignedVarInt Word" $
        UnsignedVarInt <$> limitGet 15 getUnsignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ getUnsignedVarIntSize . getUnsignedVarInt
    {-# INLINE size #-}

-- Is this instance valid at all? Is it word32 or word64 after all?
instance Bi (FixedSizeInt Word) where
    put (FixedSizeInt a) = Store.poke a -- CSL-1122 fix endianess
    {-# INLINE put #-}
    get = label "FixedSizeInt Word" $
        FixedSizeInt <$> Store.peek -- CSL-1122 fix endianess
    {-# INLINE get #-}
    size = convertSize getFixedSizeInt Store.size
    {-# INLINE size #-}

-- Word16

instance Bi (UnsignedVarInt Word16) where
    put (UnsignedVarInt a) = putUnsignedVarInt a
    {-# INLINE put #-}
    get = label "UnsignedVarInt Word16" $
        UnsignedVarInt <$> limitGet 15 getUnsignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ getUnsignedVarIntSize . getUnsignedVarInt
    {-# INLINE size #-}

-- Word32

instance Bi (UnsignedVarInt Word32) where
    put (UnsignedVarInt a) = putUnsignedVarInt a
    {-# INLINE put #-}
    get = label "UnsignedVarInt Word32" $
        UnsignedVarInt <$> limitGet 15 getUnsignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ getUnsignedVarIntSize . getUnsignedVarInt
    {-# INLINE size #-}

-- Word64

instance Bi (UnsignedVarInt Word64) where
    put (UnsignedVarInt a) = putUnsignedVarInt a
    {-# INLINE put #-}
    get = label "UnsignedVarInt Word64" $
        UnsignedVarInt <$> limitGet 15 getUnsignedVarInt'
    {-# INLINE get #-}
    size = VarSize $ getUnsignedVarIntSize . getUnsignedVarInt
    {-# INLINE size #-}

-- TinyVarInt

instance Bi TinyVarInt where
    put (TinyVarInt a) = putTinyVarInt a
    {-# INLINE put #-}
    -- Doesn't need 'limitGet' because 'TinyVarInt' is already limited to two
    -- bytes
    get = label "TinyVarInt" $
        TinyVarInt <$> getTinyVarInt'
    {-# INLINE get #-}
    size = VarSize $ getTinyVarIntSize . getTinyVarInt
    {-# INLINE size #-}

----------------------------------------------------------------------------
-- Popular basic instances
----------------------------------------------------------------------------

-- TODO get rid of boilerplate (or rewrite by hands to make it more clear)
-- I just copied most of it from here:
-- https://hackage.haskell.org/package/binary-0.8.4.1/docs/src/Data.Binary.Class.html#line-564


----------------------------------------------------------------------------
-- Primitive types
----------------------------------------------------------------------------

instance Bi () where
    put ()  = pure ()
    get     = pure ()
    size = ConstSize 0

instance Bi Bool where
    put False = putWord8 0
    put True  = putWord8 1
    get       = getWord8 >>= toBool
      where
        toBool 0 = return False
        toBool 1 = return True
        toBool c = fail ("Could not map value " ++ show c ++ " to Bool")
    size = ConstSize 1
{-

instance Bi Char where
    {-# INLINE put #-}
    put = putCharUtf8
    get = do
        let getByte = (fromIntegral :: Word8 -> Int) <$> get
            shiftL6 = flip shiftL 6 :: Int -> Int
        w <- getByte
        r <- case () of
                _ | w < 0x80  -> return w
                  | w < 0xe0  -> do
                                    x <- xor 0x80 <$> getByte
                                    return (x .|. shiftL6 (xor 0xc0 w))
                  | w < 0xf0  -> do
                                    x <- xor 0x80 <$> getByte
                                    y <- xor 0x80 <$>  getByte
                                    return (y .|. shiftL6 (x .|. shiftL6
                                            (xor 0xe0 w)))
                  | otherwise -> do
                                x <- xor 0x80 <$> getByte
                                y <- xor 0x80 <$> getByte
                                z <- xor 0x80 <$> getByte
                                return (z .|. shiftL6 (y .|. shiftL6
                                        (x .|. shiftL6 (xor 0xf0 w))))
        getChr r
      where
        getChr w
          | w <= 0x10ffff = return $! toEnum $ fromEnum w
          | otherwise = fail "Not a valid Unicode code point!"

-}

----------------------------------------------------------------------------
-- Numeric data
----------------------------------------------------------------------------

instance Bi Integer where -- FIXME: CSL-1122 fixed endianness
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi Word8 where -- FIXME: CSL-1122 fixed endianness
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi Word16 where -- FIXME: CSL-1122 fixed endianness
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi Word32 where -- FIXME: CSL-1122 fixed endianness
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi Word64 where -- FIXME: CSL-1122 fixed endianness
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi Int32 where -- FIXME: CSL-1122 fixed endianness
    size = Store.size
    put = Store.poke
    get = Store.peek

getWord8 :: Peek Word8
getWord8 = get @Word8

putWord8 :: Word8 -> Poke ()
putWord8 = put @Word8

----------------------------------------------------------------------------
-- Tagged
----------------------------------------------------------------------------

instance Bi a => Bi (Tagged s a) where
    put (Tagged a) = put a
    get = Tagged <$> get
    size = convertSize unTagged size

----------------------------------------------------------------------------
-- Containers
----------------------------------------------------------------------------

instance (Bi a, Bi b) => Bi (a, b) where
    {-# INLINE size #-}
    size = combineSize (fst, snd)
    {-# INLINE put #-}
    put (a, b) = put a *> put b
    {-# INLINE get #-}
    get = liftM2 (,) get get

instance (Bi a, Bi b, Bi c) => Bi (a, b, c) where
    {-# INLINE size #-}
    size = combineSize (view _1, view _2, view _3)
    {-# INLINE put #-}
    put (a, b, c) = put a *> put b *> put c
    {-# INLINE get #-}
    get = liftM3 (,,) get get get

{-
instance (Bi a, Bi b, Bi c, Bi d) => Bi (a, b, c, d) where
    {-# INLINE size #-}
    size = combineSize (view _1, view _2, view _3, view _4)
    {-# INLINE put #-}
    put (a, b, c, d) = put a *> put b *> put c *> put d
    {-# INLINE get #-}
    get = liftM4 (,,,) get get get get
-}

instance Bi ByteString where
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi LByteString where
    size = Store.size
    put = Store.poke
    get = Store.peek

instance Bi Text where
    size = Store.size
    put = Store.poke
    get = Store.peek

instance KnownNat n => Bi (StaticSize n ByteString) where
    size = Store.size
    put = Store.poke
    get = Store.peek

constSize :: forall a . Bi a => Int
constSize =  case size :: Size a of
  VarSize   _ -> error "constSize: VarSize"
  ConstSize a -> a

execPoke :: Poke a -> Store.PokeState -> Store.Offset -> IO Store.Offset
execPoke p ptr offset = fst <$> Store.runPoke p ptr offset

mkPoke
    :: (Store.PokeState -> Store.Offset -> IO Store.Offset)
    -> Poke ()
mkPoke f = Store.Poke (\ptr offset -> (,()) <$> f ptr offset)

instance Bi a => Bi [a] where
    size =
        VarSize $ \t -> case size :: Size a of
            ConstSize n -> (n * length t) + constSize @(UnsignedVarInt Int)
            VarSize f   -> foldl' (\acc x -> acc + f x) (constSize @(UnsignedVarInt Int)) t
    put t = do
        put (UnsignedVarInt $ length t)
        mkPoke (\ptr offset ->
            foldlM (\offset' a -> execPoke (put a) ptr offset') offset t)
    get = do
      UnsignedVarInt len <- get
      replicateM len get

instance (Bi a, Bi b) => Bi (Either a b) where
    size = case size @a of
             VarSize _ -> sizeImpl
             ConstSize s1 ->
                case size @b of
                  VarSize _ -> sizeImpl
                  ConstSize s2 ->
                    if s1 == s2
                       then ConstSize $ s1 + s2 + 1
                       else sizeImpl
      where
        sizeImpl = VarSize $ \case
                      Left a -> getSize a + 1
                      Right b -> getSize b + 1
    put (Left  a) = putWord8 0 *> put a
    put (Right b) = putWord8 1 *> put b
    get = do
        w <- getWord8
        case w of
            0 -> Left  <$> get
            1 -> Right <$> get
            _ -> fail "unexpected Either tag"


{-
-- | 'getMany n' get 'n' elements in order, without blowing the stack.
getMany :: Bi a => Int -> Get [a]
getMany n = go [] n
 where
    go xs 0 = return $! reverse xs
    go xs i = do x <- get
                 -- we must seq x to avoid stack overflows due to laziness in
                 -- (>>=)
                 x `seq` go (x:xs) (i-1)
{-# INLINE getMany #-}
-}

class CombineSize a b | a -> b where
    combineSize :: a -> Size b
-- instances are defined at the end of the file because they use TH

convertSize :: (a -> b) -> Size b -> Size a
convertSize _  (ConstSize s) = ConstSize s
convertSize conv (VarSize f) = VarSize $ f . conv

instance Bi a => Bi (NonEmpty a) where
    get = maybe (fail "Empty list") pure . nonEmpty =<< get
    put = put . toList
    size = convertSize toList size

instance (Bi a) => Bi (Maybe a) where
    size = VarSize $ \case
              Just x -> 1 + getSize x
              _ -> 1
    put Nothing  = putWord8 0
    put (Just x) = putWord8 1 *> put x
    get = do
        w <- getWord8
        case w of
            0 -> return Nothing
            _ -> Just <$> get

instance (Hashable k, Eq k, Bi k, Bi v) => Bi (HM.HashMap k v) where
    get = fmap HM.fromList get
    put = put . HM.toList
    size = convertSize HM.toList size

instance (Hashable k, Eq k, Bi k) => Bi (HashSet k) where
    get = fmap HS.fromList get
    put = put . HS.toList
    size = convertSize HS.toList size

instance (Ord k, Bi k) => Bi (Set k) where
    get = S.fromList <$> get
    put = put . S.toList
    size = convertSize S.toList size

-- Copy-pasted w/ modifications, license:
-- https://github.com/bos/vector-binary-instances/blob/master/LICENSE

instance Bi a => Bi (V.Vector a) where
    get = do
        UnsignedVarInt n <- get
        v <- pure $ unsafePerformIO $ GM.unsafeNew n
        let go 0 = return ()
            go i = do
                x <- get
                () <- pure $ unsafePerformIO $ GM.unsafeWrite v (n-i) x
                go (i-1)
        () <- go n
        pure $ unsafePerformIO $ G.unsafeFreeze v
    put v = do
        put (UnsignedVarInt (G.length v))
        G.mapM_ put v
    size = VarSize $ \v ->
        (getSize (UnsignedVarInt (G.length v))) +
        G.foldl' (\a b -> a + getSize b) 0 v

instance Bi Void where
    put = absurd
    get = fail "instance Bi Void: you shouldn't try to deserialize Void"
    size = error "instance Bi Void: you shouldn't try to serialize Void"

----------------------------------------------------------------------------
-- Other types
----------------------------------------------------------------------------

instance Bi Millisecond where
    put = put . toInteger
    get = fromInteger <$> get
    size = convertSize toInteger size

instance Bi Microsecond where
    put = put . toInteger
    get = fromInteger <$> get
    size = convertSize toInteger size

instance Bi Byte where
    put = put . toBytes
    get = fromBytes <$> get
    size = convertSize toBytes size

-- | Like 'isolate', but allows consuming less bytes than expected (just not
-- more).
-- Differences from `Store.isolate`:
--  * safely handles `Int64` length argument
--  * advances pointer only by bytes read
{-# INLINE limitGet #-}
limitGet :: Int64 -> Peek a -> Peek a
limitGet len m = Peek $ \ps ptr -> do
    let end = Store.peekStateEndPtr ps
        remaining = end `minusPtr` ptr
        len' = fromIntegral $ min (fromIntegral remaining) len
        ptr2 = ptr `plusPtr` len'
    PeekResult ptr' x <- Store.runPeek m ps ptr
    when (ptr' > ptr2) $
        throwM $ PeekException (ptr' `minusPtr` ptr2) "Overshot end of isolated bytes"
    return $ PeekResult ptr' x

-- | Isolate the input to n bytes, skipping n bytes forward. Fails if @m@
-- advances the offset beyond the isolated region.
-- Differences from `Store.isolate`:
--  * safely handles `Int64` length argument
--  * requires isolated input to be fully consumed
{-# INLINE isolate64Full #-}
isolate64Full :: Int64 -> Peek a -> Peek a
isolate64Full len m = Peek $ \ps ptr -> do
    let end = Store.peekStateEndPtr ps
        remaining = end `minusPtr` ptr
    when (len > fromIntegral remaining) $
      -- Do not perform the check on the new pointer, since it could have overflowed
#if (WORD_SIZE_IN_BITS >= 64)
      Store.tooManyBytes (fromIntegral len) remaining "isolate64"
#else
      (if len <= (maxBound :: Int)
         then Store.tooManyBytes (fromIntegral len) remaining "isolate64"
         else throwM $ PeekException 0 "")
#endif
    PeekResult ptr' x <- Store.runPeek m ps ptr
    let ptr2 = ptr `plusPtr` fromIntegral len
    when (ptr' < ptr2) $
        throwM $ PeekException (ptr2 `minusPtr` ptr') "Not all isolated bytes read"
    when (ptr' > ptr2) $
        throwM $ PeekException (ptr' `minusPtr` ptr2) "Overshot end of isolated bytes"
    return $ PeekResult ptr2 x

----------------------------------------------------------------------------
-- SafeCopy
----------------------------------------------------------------------------

-- | A helper for "Data.SafeCopy" that creates 'putCopy' given a 'Bi'
-- instance.
putCopyBi :: Bi a => a -> Contained Cereal.Put
putCopyBi x = contain $ safePut (encode x)

-- | A helper for "Data.SafeCopy" that creates 'getCopy' given a 'Bi'
-- instance.
getCopyBi :: Bi a => Text -> Contained (Cereal.Get a)
getCopyBi typeName = contain $ do
    bs <- safeGet
    case decodeFull bs of
        Left err -> (fail . T.unpack) ("getCopy@" <> typeName <> ": " <> err)
        Right x  -> return x

----------------------------------------------------------------------------
-- Binary serialization
----------------------------------------------------------------------------

-- | See `Pos.Crypto.SerTypes` for details on this types
newtype AsBinary a = AsBinary
    { getAsBinary :: ByteString
    } deriving (Show, Eq, Ord, Hashable, NFData)

instance SafeCopy (AsBinary a) where
    getCopy = contain $ AsBinary <$> safeGet
    putCopy = contain . safePut . getAsBinary

class AsBinaryClass a where
    asBinary :: a -> AsBinary a
    fromBinary :: AsBinary a -> Either Text a

fromBinaryM :: (AsBinaryClass a, MonadFail m) => AsBinary a -> m a
fromBinaryM = either (fail . T.unpack) return . fromBinary

{-
----------------------------------------------------------------------------
-- Serialization with length
----------------------------------------------------------------------------

-- | Serialize something together with its length in bytes. The length comes
-- first.
putWithLength :: Size a -> Poke a -> Poke a
putWithLength sz poke = Poke $ \ps off ->
    let (res, serialized) = runPutM act
    let len :: Int64 = BSL.length serialized
    put (UnsignedVarInt len)
    putLazyByteString serialized
    return res

-- | Read length in bytes and then parse something (which has to have exactly
-- that length).
getWithLength :: Get a -> Get a
getWithLength act = do
    -- We limit the int to 20 bytes because an UnsignedVarInt Int64 takes at
    -- most 10 bytes. (20 and not 10 because it doesn't hurt to be cautious.)
    UnsignedVarInt (len :: Int64) <- limitGet 20 get
    isolate64 len act

-- | Read length in bytes, check that it's not bigger than the limit, and
-- then parse something (which has to have exactly parsed length).
getWithLengthLimited :: Int64 -> Get a -> Get a
getWithLengthLimited lim act = do
    UnsignedVarInt (len :: Int64) <- limitGet 20 get
    if len <= lim
        then isolate64 len act
        else fail $ formatToString
                      ("getWithLengthLimited: data ("%int%" bytes) is "%
                       "bigger than the limit ("%int%" bytes)")
                      len lim

-- | Like 'putWithLength', but should only be used for things that take less
-- than @2^14@ bytes.
--
-- Uses 'TinyVarInt' for storing length, thus guaranteeing that it won't take
-- more than 2 bytes and won't be ambiguous.
putSmallWithLength :: PutM a -> PutM a
putSmallWithLength act = do
    let (res, serialized) = runPutM act
    let len :: Int64 = BSL.length serialized
    if len >= 2^(14::Int)
        then error ("putSmallWithLength: length is " <> show len <>
                    ", but maximum allowed is 16383 (2^14-1)")
        else do put (TinyVarInt (fromIntegral len))
                putLazyByteString serialized
                return res

-- | Like 'getWithLength' but for 'putSmallWithLength'.
getSmallWithLength :: Get a -> Get a
getSmallWithLength act = do
    TinyVarInt len <- get
    isolate64 (fromIntegral len) act

----------------------------------------------------------------------------
-- Other binary utils
----------------------------------------------------------------------------

getRemainingByteString :: Get ByteString
getRemainingByteString = BSL.toStrict <$> getRemainingLazyByteString
-}

getAsciiString1b :: String -> Word8 -> Peek String
getAsciiString1b typeName limit = getWord8 >>= \sz -> do
            if sz > limit
               then fail $ typeName ++ " shouldn't be more than "
                                    ++ show limit ++ " bytes long"
               else traverse checkAscii =<< BS.unpack <$> getByteString (fromIntegral sz)
  where
    checkAscii (chr . fromIntegral -> c) =
        if isAscii c
           then return c
           else fail $ "Not an ascii symbol in " ++ typeName ++ " " ++ show c

putAsciiString1b :: String -> Poke ()
putAsciiString1b str =  putWord8 (fromIntegral $ length str)
                     >> putByteString (BS.pack $ map (fromIntegral . ord) str)

-- | Compute size of something serializable in bytes.
biSize :: Bi a => a -> Byte
biSize = fromIntegral . getSize

getByteString :: Int -> Peek ByteString
getByteString i = reifyNat (fromIntegral i) $ \(_ :: Proxy n) -> unStaticSize <$> (Store.peek :: Peek (StaticSize n ByteString))

putByteString :: ByteString -> Poke ()
putByteString bs = reifyNat (fromIntegral $ BS.length bs) $ \(_ :: Proxy n) ->
                      Store.poke (Store.toStaticSizeEx bs :: StaticSize n ByteString)

----------------------------------------------------------------------------
-- CombineSize instances
----------------------------------------------------------------------------

-- this could be written as “CombineSize (x -> a, x -> b) x”, but the way we
-- do it here leads to better type inference because this instance guarantees
-- that it's the *only* possible instance for a tuple of length 2
instance (Bi a, xa ~ (x -> a),
          Bi b, xb ~ (x -> b))
         => CombineSize (xa, xb) x where
    combineSize (a, b) = Store.combineSizeWith a b size size
    {-# INLINE combineSize #-}

{- Generate CombineSize instances for larger sizes.

Generated instances look like this:

    instance (Bi p1, x1 ~ (xt -> p1),
              Bi p2, x2 ~ (xt -> p2))
            => CombineSize (x1, x2) xt where
       combineSize (f1, f2) =
           case (size :: Size p1, size :: Size p2) of
               (ConstSize s1, ConstSize s2) -> ConstSize (s1 + s2)
               _ -> VarSize (\xv -> getSize (f1 xv) + getSize (f2 xv))
       {-# INLINE combineSize #-}
-}
forM [3..10] $ \n -> do
    -- An utility to sum a bunch of expressions
    let sumE = foldr1 (infixApp [|(+)|])
    -- names
    xt <- newName "xt"
    xv <- newName "xv"
    ps <- newNames "p" n
    xs <- newNames "x" n
    fs <- newNames "f" n
    ss <- newNames "s" n
    -- constraints
    let biConstraints = [ [t|Bi $p|] | p <- map varT ps ]
        eqConstraints = [ [t|$x ~ ($(varT xt) -> $p)|] | p <- map varT ps
                                                       | x <- map varT xs ]
    -- instance head
    let instHead = [t|CombineSize $(toTupleT (map varT xs)) $(varT xt)|]
    -- combineSize argument
    let funArg = tupP (map varP fs)
    -- case scrutinee
    let caseExp = tupE [ [|size :: Size $p|] | p <- map varT ps ]
    -- the first case pattern and the result
    let casePat1 = tupP [ [p|ConstSize $s|] | s <- map varP ss ]
    let caseRes1 = appE [|ConstSize|] (sumE (map varE ss))
    -- the second case pattern and the result
    let casePat2 = wildP
    let caseRes2 = appE [|VarSize|] (lam1E (varP xv)
                       (sumE [ [|getSize ($f $(varE xv))|] | f <- map varE fs ]))
    -- the inline pragma
    let inlinePragma = pragInlD 'combineSize Inline FunLike AllPhases
    -- all together
    instanceD
        (sequence (biConstraints ++ eqConstraints))
        instHead
        [ funD 'combineSize [
              clause [funArg] (normalB $ caseE caseExp
                  [ match casePat1 (normalB caseRes1) []
                  , match casePat2 (normalB caseRes2) [] ]) [] ]
        , inlinePragma ]
