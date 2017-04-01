module Pos.Ssc.Class.Helpers
       ( SscHelpersClass (..)
       ) where

import           Data.Tagged           (Tagged)
import           Universum

import           Pos.Core.Types        (EpochIndex)
import           Pos.Ssc.Class.Types   (Ssc (..))
import           Pos.Types.Block.Types (MainBlockHeader)

class Ssc ssc => SscHelpersClass ssc where
    sscVerifyPayload ::
        Tagged ssc ( Either EpochIndex (MainBlockHeader ssc) ->
                     SscPayload ssc ->
                     Either (SscVerifyError ssc) ())
