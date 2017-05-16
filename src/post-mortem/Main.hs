import qualified Data.GraphViz.Commands.IO as G
import qualified Data.Map.Strict           as M
import           System.IO                 (hPutStrLn)

import           Statistics
import           Universum


main :: IO ()
main = do
    [logDir, graphFile] <- getArgs
    err $ "logs directory: " ++ show logDir
    (rc, g) <- runJSONFold logDir $ (,) <$> receivedCreatedF <*> graphF
    let total = M.size rc
    let included = sort $ mapMaybe snd $ M.toList rc
    err $ "total number of received transactions: " ++ show total
    err $ "included in blockchain: " ++ show (length included)
    err $ "lost transactions: " ++ show (total - length included)
    for_ included print 
    err $ "writing graph to: " ++ show graphFile
    void $ G.writeDotFile graphFile g
  where
    err :: String -> IO ()
    err = hPutStrLn stderr
