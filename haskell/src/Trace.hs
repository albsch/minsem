module Trace (trace) where

import qualified Debug.Trace as T

traceFlag :: Bool
traceFlag = False

trace :: String -> a -> a
trace = if traceFlag then T.trace else noTrace

noTrace :: String -> a -> a
noTrace _ x = x
