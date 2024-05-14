{-# OPTIONS_GHC -F -pgmF htfpp #-}
module BasicTests (htf_thisModulesTests) where

import Ty
import Iface
import qualified Minsem as M
import Pretty
import System.Timeout
import Control.Exception (evaluate)
import Utils
import Test.Framework

subTyTimeout :: Int
subTyTimeout = 2 * 1000 * 1000 -- in microseconds

-- t1 <= t2 iff t1 /\ not t2 = empty
isSubTy :: Monad m => SemIface t s m -> Ty -> Ty -> m (Bool, t)
isSubTy impl t1 t2 = do
    t <- tyRep impl (TyInter t1 (TyNeg t2))
    b <- isEmpty impl t
    pure (b, t)

assertSubTy :: (Pretty t, Pretty s, Monad m) => SemIface t s m -> Ty -> Ty -> Bool -> IO ()
assertSubTy impl t1 t2 b = do
    putStrLn ("Checking " ++ show t1 ++ " <= " ++ show t2 ++
              " (expected " ++ show b ++ ")")
    x <- timeout subTyTimeout $ timeIt $ evaluate (run impl (isSubTy impl t1 t2))
    case x of
        Nothing ->
            assertFailure ("Subtype checked timed out.")
        Just (((res, t), s), delta) -> do
            putStrLn ("Result for " ++ show t1 ++ " <= " ++ show t2 ++ ": " ++ show res ++
                ", " ++ show delta)
            assertEqualVerbose
                ("Internal type: " ++ showPretty t ++ "\n" ++
                 show (indent 2 (pretty s)))
                b res

basicTests :: (Pretty t, Pretty s, Monad m) => SemIface t s m -> IO ()
basicTests impl = do
    subAssert $ assertSubTy impl TyTop TyTop True
    subAssert $ assertSubTy impl TyTop TyBottom False
    subAssert $ assertSubTy impl TyBottom TyTop True
    let t1 = TyAtom False
        t2 = TyDiff TyAnyAtom TyTop
    subAssert $ assertSubTy impl t1 TyBottom False
    subAssert $ assertSubTy impl t2 TyBottom True
    subAssert $ assertSubTy impl (TyProd t1 t2) TyBottom True

printRepr :: (Pretty t, Pretty s, Monad m) => SemIface t s m -> Ty -> IO ()
printRepr impl t = do
    let (r, s) = run impl $ tyRep impl t
    putStrLn (show t ++ ": " ++ showPretty r)
    print (indent 2 (pretty s))

test_basicMinsem :: IO ()
test_basicMinsem = do
    printRepr M.impl TyTop
    printRepr M.impl TyBottom
    printRepr M.impl (TyAtom True)
    printRepr M.impl (TyAtom False)
    printRepr M.impl (TyUnion TyTop TyTop)
    printRepr M.impl (TyInter TyTop TyTop)
    printRepr M.impl (TyNeg TyTop)
    printRepr M.impl (TyInter TyTop (TyNeg TyTop))
    basicTests M.impl
