module Utils (
    nubHash,
    timeIt
) where

import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Time

nubHash :: Hashable a => [a] -> [a]
nubHash = go HashSet.empty []
  where
    go _ acc [] = reverse acc
    go s acc (x:xs) =
        if x `HashSet.member` s
            then go s acc xs
            else go (HashSet.insert x s) (x:acc) xs

timeIt :: IO a -> IO (a, NominalDiffTime)
timeIt action = do
  start <- getCurrentTime
  x <- action
  end <- getCurrentTime
  pure (x, end `diffUTCTime` start)
