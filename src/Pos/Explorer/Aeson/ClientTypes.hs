{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Pos.Explorer.Aeson.ClientTypes
       (
       ) where

import           Data.Aeson.TH                (defaultOptions, deriveJSON,
                                               deriveToJSON)
import           Pos.Aeson                    ()
import           Pos.Explorer.Web.ClientTypes (CAddress, CAddressSummary,
                                               CBlockEntry, CBlockSummary,
                                               CHash, CNetworkAddress, CTxBrief,
                                               CTxEntry, CTxId, CTxSummary)
import           Pos.Explorer.Web.Error       (ExplorerError)





deriveJSON defaultOptions ''CHash
deriveJSON defaultOptions ''CAddress
deriveJSON defaultOptions ''CTxId

deriveToJSON defaultOptions ''ExplorerError
deriveToJSON defaultOptions ''CBlockEntry
deriveToJSON defaultOptions ''CTxEntry
deriveToJSON defaultOptions ''CTxBrief
deriveToJSON defaultOptions ''CAddressSummary
deriveToJSON defaultOptions ''CBlockSummary
deriveToJSON defaultOptions ''CNetworkAddress
deriveToJSON defaultOptions ''CTxSummary
