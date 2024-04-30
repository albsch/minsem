module Utils (
    nubHash,
    noTrace
) where

import Data.Hashable
import qualified Data.HashSet as HashSet

nubHash :: Hashable a => [a] -> [a]
nubHash = go HashSet.empty []
  where
    go _ acc [] = reverse acc
    go s acc (x:xs) =
        if x `HashSet.member` s
            then go s acc xs
            else go (HashSet.insert x s) (x:acc) xs

noTrace :: String -> a -> a
noTrace _ x = x
