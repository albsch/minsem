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
import Control.Monad

isEmptyTimeout :: Int
isEmptyTimeout = 2 * 1000 * 1000 -- in microseconds

isEmpty :: Monad m => SemIface t s m -> Ty -> m (Bool, t)
isEmpty impl ty = do
    t <- tyRep impl ty
    b <- I.isEmpty impl t
    pure (b, t)

checkCduceTestCase ::
    (Pretty t, Pretty s, Monad m) => SemIface t s m -> (Int, (Ty, Bool)) -> IO (Maybe String)
checkCduceTestCase impl (idx, (ty, cduceRes)) = do
    putStrLn ("Running cduce test " ++ show idx ++ " (" ++ show cduceRes ++ "): "
                ++ showPretty ty)
    x <- timeout isEmptyTimeout $ timeIt $ evaluate (I.run impl (isEmpty impl ty))
    case x of
        Nothing -> do
            let msg = "Timeout in cduce check " ++ show idx ++ ": " ++ showPretty ty
            pure $ Just msg
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
                    assertFailure "test failed"
            pure Nothing

readTestCases :: FilePath -> IO [(Ty, Bool)]
readTestCases path = do
    content <- T.readFile path
    pure (mapMaybe parseLine (T.lines content))
    where
        parseLine (T.strip -> t) =
            if T.null t then Nothing else Just (read (T.unpack t))

test_cduce :: IO ()
test_cduce = do
    let path = "cduce_test_cases.txt"
    testCases <- readTestCases path
    let total = length testCases
    putStrLn ("Found " ++ show total ++ " test cases in " ++ path)
    timeouts <- reverse <$> foldM runTest [] (zip [1..] testCases)
    let n = length timeouts
    when (n > 0) $ do
        putStrLn (show n ++ " test cases timed out!")
        forM_ timeouts $ \s -> putStrLn ("- " ++ s)
        assertFailure "timeouts"
    where
        runTest timeouts testCase = do
            res <- checkCduceTestCase M.impl testCase
            pure (maybeToList res ++ timeouts)
