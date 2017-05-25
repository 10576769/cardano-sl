{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE PolyKinds    #-}
{-# LANGUAGE TypeFamilies #-}

-- | Default implementation of WithNodeContext.

module Pos.Context.Holder
       ( ContextHolder
       , runContextHolder
       , defaultRelayLogCallback
       ) where

import qualified Control.Monad.Ether           as Ether.E
import           Formatting                    (sformat, shown, (%))
import           Mockable                      (Catch, Mockable, catchAll)
import           System.Wlog                   (WithLogger, logWarning)
import           Universum                     hiding (catchAll)

import           Pos.Communication.Types.Relay (RelayLogCallback, RelayLogEvent (..))
import           Pos.Context.Class             (WithNodeContext)
import           Pos.Context.Context           (NodeContext (..))
import           Pos.Util.Context              (ContextHolder', ContextTagK (..))
import           Pos.Util.JsonLog              (MonadJL (..), appendJL, JLEvent (..))
import           Pos.Util.Util                 (ether)

-- | Wrapper for monadic action which brings 'NodeContext'.
type ContextHolder ssc = ContextHolder' (ContextHolderTrans ssc)

type ContextHolderTrans ssc = ReaderT (NodeContext ssc)

-- | Run 'ContextHolder' action.
runContextHolder :: NodeContext ssc -> ContextHolder ssc m a -> m a
runContextHolder = flip (Ether.E.runReaderT (Proxy @'ContextTag))

instance
    (MonadIO m, Mockable Catch m, WithLogger m, ContextHolderTrans ssc ~ t) =>
        MonadJL (ContextHolder' t m)
  where
    jlLog ev = do
        mv <- ether $ asks ncJLFile
        appendJL mv ev `catchAll` \e ->
            logWarning $ sformat ("Can't write to json log: "%shown) e

defaultRelayLogCallback :: (WithNodeContext ssc m, MonadJL m, MonadIO m) => RelayLogCallback m
defaultRelayLogCallback e = do 
    jlLog $ JLRelayEvent e
    case e of
        RelayQueueFull        -> Ether.E.asks (Proxy :: Proxy 'ContextTag) ncOnRelayQueueFull >>= liftIO
        EnqueueDequeueTime dt -> Ether.E.asks (Proxy :: Proxy 'ContextTag) ncOnRelayDequeue >>= liftIO . ($ dt)
