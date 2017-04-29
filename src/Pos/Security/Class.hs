module Pos.Security.Class
       ( SecurityWorkersClass (..)
       ) where

import           Data.Tagged                (Tagged)
import           Universum

import           Pos.Communication.Protocol (OutSpecs, WorkerSpec)
import           Pos.Ssc.Class.Types        (Ssc)
import           Pos.WorkMode               (WorkMode)

class Ssc ssc => SecurityWorkersClass ssc where
    securityWorkers :: WorkMode ssc m => Tagged ssc ([WorkerSpec m], OutSpecs)
