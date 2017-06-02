{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

-- | Monadic represantion of something that has @json@ journaled log
-- of operations.

module Pos.Util.JsonLog
       ( JLEvent(..)
       , JLBlock (..)
       , JLTxS (..)
       , JLTxR (..)
       , JLMemPool (..)
       , JLTimedEvent (..)
       , jlCreatedBlock
       , jlAdoptedBlock
       , MonadJL
       , jlLog
       , appendJL
       , fromJLSlotId
       , JLFile(..)
       , usingJsonLogFilePath
       ) where

import           Control.Concurrent.MVar (withMVar)
import           Data.Aeson              (encode, FromJSON (..), withObject, (.:),
                                          (.:?), genericParseJSON)
import           Data.Aeson.TH           (deriveJSON, deriveToJSON)
import qualified Data.ByteString.Lazy     as LBS
import qualified Ether
import           Formatting              (sformat)
import           Serokell.Aeson.Options  (defaultOptions)
import           System.IO               (hClose)
import           System.Wlog             (CanLog, HasLoggerName)
import           Universum               hiding (catchAll)

import           Pos.Binary.Block        ()
import           Pos.Binary.Core         ()
import           Pos.Communication.Relay.Logic (InvReqDataFlowLog)
import           Pos.Crypto              (Hash, hash, hashHexF)
import           Pos.Ssc.Class.Types     (Ssc)
import           Pos.Types               (BiSsc, Block, SlotId (..), blockHeader,
                                          blockTxs, epochIndexL, gbHeader, gbhPrevBlock,
                                          headerHash, headerSlot)
import           Pos.Txp.MemState.Types  (MemPoolModifyReason (Custom, Unknown))
import           Pos.Util.TimeWarp       (currentTime)

type BlockId = Text
type TxId = Text
type JLSlotId = (Word64, Word16)

-- | Json log of one block with corresponding 'BlockId'.
data JLBlock = JLBlock
    { jlHash      :: BlockId
    , jlPrevBlock :: BlockId
    , jlTxs       :: [TxId]
    , jlSlot      :: JLSlotId
    } deriving Show

-- | Json log of one transaction sent from the (light) wallet.
data JLTxS = JLTxS
    { jlsNodeId :: Text
    , jlsTxId   :: Text
    , jlsInvReq :: InvReqDataFlowLog
    } deriving Show

-- | Json log of one transaction being received by a node.
data JLTxR = JLTxR
    { jlrTxId     :: Text
    , jlrReceived :: Integer
    , jlrError    :: Maybe Text
    } deriving Show

-- | Get 'SlotId' from 'JLSlotId'.
fromJLSlotId :: JLSlotId -> SlotId
fromJLSlotId (ep, sl) = SlotId (fromIntegral ep) (fromIntegral sl)

-- | Json log of one mempool modification.
data JLMemPool = JLMemPool
    { -- | Reason for modifying the mempool
      jlmReason      :: MemPoolModifyReason
      -- | Queue length when trying to modify the mempool (not including this
      --   modifier, so it could be 0).
    , jlmQueueLength :: Int
      -- | Time spent waiting for the lock (microseconds)
    , jlmWait        :: Integer
      -- | Time spent doing the modification (microseconds, while holding the lock).
    , jlmModify      :: Integer
      -- | Size of the mempool before the modification.
    , jlmSizeBefore  :: Int
      -- | Size of the mempool after the modification.
    , jlmSizeAfter   :: Int
      -- | How much memory was allocated during the modification.
    , jlmAllocated   :: Int
    } deriving Show

-- | Json log event.
data JLEvent = JLCreatedBlock JLBlock
             | JLAdoptedBlock BlockId
             | JLTpsStat Int
             | JLTxSent JLTxS
             | JLTxReceived JLTxR 
             | JLMemPoolEvent JLMemPool
  deriving (Show, Generic)

-- | 'JLEvent' with 'Timestamp' -- corresponding time of this event.
data JLTimedEvent = JLTimedEvent
    { jlTimestamp :: Integer
    , jlEvent     :: JLEvent
    } deriving (Show)

$(deriveJSON defaultOptions ''JLBlock)
$(deriveJSON defaultOptions ''JLTxS)
$(deriveJSON defaultOptions ''JLTxR)
$(deriveJSON defaultOptions ''JLMemPool)
$(deriveToJSON defaultOptions ''JLEvent)
$(deriveJSON defaultOptions ''JLTimedEvent)

instance FromJSON JLEvent where

    parseJSON = \v -> 
        (    (genericParseJSON defaultOptions v)
         -- Second iteration of JLMemPoolEvent: the 'reason' was Text and
         -- the allocation field was optional.
         <|> (flip (withObject "JLEvent") v $ \oEvent -> do
                 oMemPool <- oEvent .: "memPoolEvent"
                 reason <- oMemPool .: "reason"
                 queueLength <- oMemPool .: "queueLength"
                 wait <- oMemPool .: "wait"
                 modify_ <- oMemPool .: "modify"
                 sizeBefore <- oMemPool .: "sizeBefore"
                 sizeAfter <- oMemPool .: "sizeAfter"
                 mAllocated <- oMemPool .:? "allocated"
                 pure $ JLMemPoolEvent $ JLMemPool
                     { jlmReason = Custom reason
                     , jlmQueueLength = queueLength
                     , jlmWait = wait
                     , jlmModify = modify_
                     , jlmSizeBefore = sizeBefore
                     , jlmSizeAfter = sizeAfter
                     , jlmAllocated = maybe 0 identity mAllocated
                     }
             )
         -- First iteration of JLMemPoolEvent: only the mempool size was recorded.
         <|> (flip (withObject "JLEvent") v $ \o -> do
                 sizeAfter <- o .: "memPoolSize"
                 pure $ JLMemPoolEvent $ JLMemPool
                     { jlmReason = Unknown
                     , jlmQueueLength = 0
                     , jlmWait = 0
                     , jlmModify = 0
                     , jlmSizeBefore = 0
                     , jlmSizeAfter = sizeAfter
                     , jlmAllocated = 0
                     }
             )
        )

-- | Return event of created block.
jlCreatedBlock :: BiSsc ssc => Block ssc -> JLEvent
jlCreatedBlock block = JLCreatedBlock $ JLBlock {..}
  where
    jlHash = showHash $ headerHash block
    jlPrevBlock = showHash $ either (view gbhPrevBlock) (view gbhPrevBlock) (block ^. blockHeader)
    jlSlot = (fromIntegral $ siEpoch slot, fromIntegral $ siSlot slot)
    jlTxs = case block of
              Left _   -> []
              Right mB -> map fromTx . toList $ mB ^. blockTxs
    slot :: SlotId
    slot = either (\h -> SlotId (h ^. epochIndexL) 0) (view $ gbHeader . headerSlot) $ block
    fromTx = showHash . hash

showHash :: Hash a -> Text
showHash = sformat hashHexF

-- | Returns event of created 'Block'.
jlAdoptedBlock :: Ssc ssc => Block ssc -> JLEvent
jlAdoptedBlock = JLAdoptedBlock . showHash . headerHash

-- | Append event into log by given 'Handle'
appendJL :: (MonadIO m) => JLFile -> JLEvent -> m ()
appendJL (JLFile mMVar) ev = whenJust mMVar $ \(v, decide) -> do
    shouldLog <- liftIO $ decide ev
    when shouldLog $ do
        time <- currentTime
        let codedEvent = encode $ JLTimedEvent (fromIntegral time) ev
        liftIO $ withMVar v $ \choice -> case choice of
            Left fp -> bracket (openFile fp WriteMode) hClose (flip LBS.hPut codedEvent)
            Right h -> LBS.hPut h codedEvent

-- | Note: not an ideal representation. One branch used
--     Maybe (MVar FilePath)
--   and another used
--     Maybe (MVar Handle)
--   so to make merging simpler they were unified.
--
--   If a FilePath is given, the file will be opened, written, and closed
--   at each 'jlLog', whereas giving a handle allows the caller to control
--   acquision and release, possibly holding the file open for the duration
--   of the program.
newtype JLFile = JLFile (Maybe (MVar (Either FilePath Handle), JLEvent -> IO Bool))

-- | Monad for things that can log Json log events.
type MonadJL m =
    ( Ether.MonadReader' JLFile m
    , MonadIO m
    , HasLoggerName m
    , CanLog m )

jlLog :: MonadJL m => JLEvent -> m ()
jlLog ev = Ether.ask' >>= flip appendJL ev

usingJsonLogFilePath
    :: ( MonadIO m, MonadMask m )
    => Maybe (FilePath, JLEvent -> IO Bool)
    -> Ether.ReaderT' JLFile m a
    -> m a
usingJsonLogFilePath mPathAndDecider act = case mPathAndDecider of
    Nothing   -> Ether.runReaderT' act (JLFile Nothing)
    Just (path, decider) -> bracket (openFile path WriteMode) (liftIO . hClose) $ \h -> do
        hMV <- newMVar (Right h)
        Ether.runReaderT' act (JLFile (Just (hMV, decider)))
