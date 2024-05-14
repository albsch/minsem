{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  MultiWayIf #-}
module CduceTestGen where

import Ty
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Monad.IO.Class
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Process
import System.Exit (exitFailure)
import System.Directory

cduceRepr :: Ty -> T.Text
cduceRepr t =
    case t of
      TyTop -> "Any"
      TyBottom -> "Empty"
      TyAtom True -> "`True"
      TyAtom False -> "`False"
      TyAnyAtom -> "`True | `False"
      TyProd t1 t2 -> parens (cduceRepr t1 <> "," <> cduceRepr t2)
      TyAnyProd -> "(Any, Any)"
      TyUnion t1 t2 -> parens (cduceRepr t1) <> "|" <> parens (cduceRepr t2)
      TyInter t1 t2 -> parens (cduceRepr t1) <> "&" <> parens (cduceRepr t2)
      TyDiff t1 t2 -> parens (cduceRepr t1) <> "\\" <> parens (cduceRepr t2)
      TyNeg t -> "Any \\ " <> parens (cduceRepr t)
    where
        parens x = "(" <> x <> ")"

cduceIsEmpty :: Ty -> IO Bool
cduceIsEmpty t = do
    let input = "debug subtype ((" <> cduceRepr t <> ") Empty);;"
    output <- T.pack <$> readProcess "cduce" [] (T.unpack input)
    cduceResult <- getCduceResult input output
    if | "false" `T.isSuffixOf` cduceResult -> pure False
       | "true" `T.isSuffixOf` cduceResult -> pure True
       | otherwise -> unexpectedCduceOutput input output
    where
        getCduceResult :: T.Text -> T.Text -> IO T.Text
        getCduceResult input output =
            case reverse (lines (T.unpack (T.strip output))) of
                result : _ -> pure (T.strip (T.pack result))
                _ -> unexpectedCduceOutput input output
        unexpectedCduceOutput input output = do
            putStrLn ("Unexpected output from cduce\n" ++ delim ++ "\n" ++
                    T.unpack output ++ "\n" ++ delim ++ "\n" ++
                    "\nInput: " ++ T.unpack input)
            exitFailure
        delim = "--------------------------------"

appendResult :: FilePath -> Ty -> Bool -> IO ()
appendResult path t b = do
    exists <- doesFileExist path
    content <-
        if exists then T.readFile path else pure ""
    let newContent = append content (T.pack (show (t, b)))
    T.writeFile path newContent
    where
        append t1 t2 =
            let t1' = T.strip t1
            in if T.null t1' then t2 else t1' <> "\n" <> t2

genTestsProp :: FilePath -> Bool -> Ty -> Property
genTestsProp path expected t = monadicIO $ do
    b <- liftIO $ cduceIsEmpty t
    pre (b == expected) -- only keep tests with the expected result
    liftIO $ appendResult path t b

genTests :: FilePath -> Int -> Int -> IO ()
genTests path emptyCount nonEmptyCount = do
    putStrLn ("Generating " ++ show emptyCount ++ " test cases for empty")
    qcSuccess (withMaxSuccess emptyCount (genTestsProp path True))
    putStrLn ("Generating " ++ show nonEmptyCount ++ " test cases for non-empty")
    qcSuccess (withMaxSuccess nonEmptyCount (genTestsProp path False))
    where
        qcSuccess prop = do
            r <- quickCheckResult prop
            case r of
                Success {} -> pure ()
                _ -> do
                    putStrLn ("QuickCheck failed to generate the test cases: " ++ show r)
                    exitFailure


