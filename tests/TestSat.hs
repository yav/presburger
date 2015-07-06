
import Data.Sat
import System.Environment
import Data.List
import qualified Data.IntMap as IntMap

main :: IO ()
main = mapM_ testFile =<< getArgs

testFile file =
  do putStr (show file ++ " ")
     txt <- readFile file
     let lss = dimacs txt
     case checkSat lss of
       Nothing -> putStrLn "unsat"
       Just m | Just bad <- find (unsatClause m) lss
                        -> error $ unlines [ "BUG", show m, show bad ]
              | otherwise -> putStrLn "sat"
  where
  val m x = if x > 0 then m IntMap.! x else not (m IntMap.! negate x)
  unsatClause m = all (not . val m)

dimacs :: String -> [[Lit]]
dimacs = map (map read . init) . filter (not . skip) . map words . fst . break (=="%") . lines
  where
  skip [] = True
  skip ("c" : _) = True
  skip ("p" : _) = True
  skip _  = False

