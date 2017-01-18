{-# LANGUAGE TemplateHaskell #-}

-- | Types related to DB.

module Pos.DB.Types
       (
         -- * General types.
         DB (..)
       , NodeDBs (..)
       , blockDB
       , gStateDB
       , lrcDB
       , miscDB

        -- * Block DB related types.
       , StoredBlock (..)

        -- * LRC related types.
       , LeadersStorage (..)
       , GtRichmenStorage (..)

        -- * Update System related types.
       ) where

import           Control.Lens     (makeLenses)
import qualified Database.RocksDB as Rocks
import           Universum

import           Pos.Lrc.Types    (RichmenStake)
import           Pos.Types        (Block, EpochIndex, SlotLeaders)

----------------------------------------------------------------------------
-- General
----------------------------------------------------------------------------

-- should we replace `rocks` prefix by other or remove it at all?
data DB ssc = DB
    { rocksReadOpts  :: !Rocks.ReadOptions
    , rocksWriteOpts :: !Rocks.WriteOptions
    , rocksOptions   :: !Rocks.Options
    , rocksDB        :: !Rocks.DB
    }

data NodeDBs ssc = NodeDBs
    { _blockDB  :: !(DB ssc) -- ^ Blocks, block index, undo data.
    , _gStateDB :: !(DB ssc) -- ^ Global state corresponding to some tip.
    , _lrcDB    :: !(DB ssc) -- ^ Data computed by LRC.
    , _miscDB   :: !(DB ssc) -- ^ Everything small and insignificant
    }

makeLenses ''NodeDBs

----------------------------------------------------------------------------
-- Blocks DB
----------------------------------------------------------------------------

-- Todo maybe remove this wrapper at all?
data StoredBlock ssc = StoredBlock
    { sbBlock  :: !(Block ssc)  -- ^ Block itself.
    } deriving (Generic)

----------------------------------------------------------------------------
-- LRC
----------------------------------------------------------------------------

data LeadersStorage ssc = LeadersStorage
    { lrcEpoch   :: !EpochIndex
    , lrcLeaders :: !SlotLeaders
    } deriving (Generic)

data GtRichmenStorage ssc = GtRichmenStorage
    { gtRichmenEpoch :: !EpochIndex
    , gtRichmen      :: !RichmenStake
    } deriving (Generic)
