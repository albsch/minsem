module Trace (trace) where

-- import qualified Debug.Trace as Trace

trace :: String -> a -> a
trace = noTrace

noTrace :: String -> a -> a
noTrace _ x = x
