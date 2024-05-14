{-# LANGUAGE  ViewPatterns #-}
{-# OPTIONS_GHC -F -pgmF htfpp #-}
module CduceTests where

import Test.Framework
import Ty
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Maybe
import Pretty
import Iface (SemIface)
import qualified Iface as I
import System.Timeout
import Control.Exception
import qualified Minsem as M
import Utils

isEmptyTimeout :: Int
isEmptyTimeout = 2 * 1000 * 1000 -- in microseconds

isEmpty :: Monad m => SemIface t s m -> Ty -> m (Bool, t)
isEmpty impl ty = do
    t <- tyRep impl ty
    b <- I.isEmpty impl t
    pure (b, t)

checkCduceTestCase ::
    (Pretty t, Pretty s, Monad m) => SemIface t s m -> (Int, (Ty, Bool)) -> IO ()
checkCduceTestCase impl (idx, (ty, cduceRes)) = do
    putStrLn ("Running cduce test " ++ show idx ++ " (" ++ show cduceRes ++ "): "
                ++ showPretty ty)
    x <- timeout isEmptyTimeout $ timeIt $ evaluate (I.run impl (isEmpty impl ty))
    case x of
        Nothing ->
            assertFailure ("Subtype checked timed out.")
        Just (((myRes, t), s), delta) -> do
            let msg =
                    "Type: " ++ showPretty ty ++ "\n" ++
                    "My isEmpty: " ++ show myRes ++ "\n" ++
                    "Cduce isEmpty: " ++ show cduceRes ++ "\n" ++
                    "Internal type: " ++ showPretty t ++ "\n" ++
                    show (indent 2 (pretty s))
            if cduceRes == myRes
                then putStrLn ("Cduce test " ++ show idx ++ " OK (" ++ show delta ++ ")")
                else do
                    putStrLn msg
                    fail "mismatch"

readTestCases :: FilePath -> IO [(Ty, Bool)]
readTestCases path = do
    content <- T.readFile path
    pure (mapMaybe parseLine (T.lines content))
    where
        parseLine (T.strip -> t) =
            if T.null t then Nothing else Just (read (T.unpack t))

test_cduce :: IO ()
test_cduce = do
    testCases <- readTestCases "cduce_test_cases.txt"
    mapM_ (checkCduceTestCase M.impl) (zip [1..] testCases)
