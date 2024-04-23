module Utils (
    nubHash
) where

import Data.Hashable
import qualified Data.HashSet as HashSet

nubHash :: Hashable a => [a] -> [a]
nubHash = go HashSet.empty []
  where
    go s acc [] = reverse acc
    go s acc (x:xs) =
        if x `HashSet.member` s
            then go s acc xs
            else go s (x:acc) xs
