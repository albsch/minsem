{-# OPTIONS_GHC -F -pgmF htfpp #-}
module BasicTests (htf_thisModulesTests) where

import Ty
import qualified Iface as I
import qualified Minsem as M
import Pretty
import System.Timeout
import Control.Exception (evaluate)
import Utils
import Test.Framework hiding (assertEmpty)

runTimeout :: Int
runTimeout = 2 * 1000 * 1000 -- in microseconds

-- t1 <= t2 iff t1 /\ not t2 = empty
isSubTy :: Monad m => I.SemIface t s m -> Ty -> Ty -> m (Bool, t)
isSubTy impl t1 t2 = do
    t <- tyRep impl (TyInter t1 (TyNeg t2))
    b <- I.isEmpty impl t
    pure (b, t)

isEmpty :: Monad m => I.SemIface t s m -> Ty -> m (Bool, t)
isEmpty impl ty = do
    t <- tyRep impl ty
    b <- I.isEmpty impl t
    pure (b, t)

assertEmpty :: (Pretty t, Pretty s, Monad m) => I.SemIface t s m -> Ty -> Bool -> IO ()
assertEmpty impl ty b = do
    putStrLn ("Checking that isEmpty" ++ show ty ++ " returns " ++ show b)
    x <- timeout runTimeout $ timeIt $ evaluate (I.run impl (isEmpty impl ty))
    case x of
        Nothing ->
            assertFailure ("isEmpty timed out.")
        Just (((res, t), s), delta) -> do
            putStrLn ("isEmpty " ++ show ty ++ ": " ++ show res ++ " (" ++ show delta ++ ")")
            assertEqualVerbose
                ("Internal type: " ++ showPretty t ++ "\n" ++
                 show (indent 2 (pretty s)))
                b res

assertSubTy :: (Pretty t, Pretty s, Monad m) => I.SemIface t s m -> Ty -> Ty -> Bool -> IO ()
assertSubTy impl t1 t2 b = do
    putStrLn ("Checking " ++ show t1 ++ " <= " ++ show t2 ++
              " (expected " ++ show b ++ ")")
    x <- timeout runTimeout $ timeIt $ evaluate (I.run impl (isSubTy impl t1 t2))
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

assertEquiv :: (Pretty t, Pretty s, Monad m) => I.SemIface t s m -> Ty -> Ty -> IO ()
assertEquiv impl t1 t2 = do
    assertSubTy impl t1 t2 True
    assertSubTy impl t2 t1 True

basicTests :: (Pretty t, Pretty s, Monad m) => I.SemIface t s m -> IO ()
basicTests impl = do
    subAssert $ assertSubTy impl TyTop TyTop True
    subAssert $ assertSubTy impl TyTop TyBottom False
    subAssert $ assertSubTy impl TyBottom TyTop True
    let t1 = TyAtom False
        t2 = TyDiff TyAnyAtom TyTop
    subAssert $ assertSubTy impl t1 TyBottom False
    subAssert $ assertSubTy impl t2 TyBottom True
    subAssert $ assertSubTy impl (TyProd t1 t2) TyBottom True
    let t3 = TyProd TyAnyProd TyAnyProd
        t4 = TyDiff (TyAtom True) t3
        t5 = TyNeg t4
        t6 = TyDiff (TyAtom False) (TyNeg t4 )
    subAssert $ assertEquiv impl t4 (TyAtom True)
    subAssert $ assertEquiv impl (TyNeg (TyAtom True)) (TyUnion (TyAtom False) TyAnyProd)
    subAssert $ assertEquiv impl t5 (TyUnion (TyAtom False) TyAnyProd)
    subAssert $ assertEmpty impl t6 True

printRepr :: (Pretty t, Pretty s, Monad m) => I.SemIface t s m -> Ty -> IO ()
printRepr impl t = do
    let (r, s) = I.run impl $ tyRep impl t
    putStrLn (show t ++ ": " ++ showPretty r)
    print (indent 2 (pretty s))

test_prettyType :: IO ()
test_prettyType = do
    assertPrettyTy (TyUnion TyTop TyTop) "top | top"
    assertPrettyTy (TyUnion TyTop (TyUnion TyTop TyTop)) "top | (top | top)"
    assertPrettyTy (TyUnion TyTop (TyInter TyTop TyTop)) "top | top & top"
    assertPrettyTy (TyUnion TyTop (TyDiff TyTop TyTop)) "top | (top - top)"
    assertPrettyTy (TyNeg TyTop) "~top"
    assertPrettyTy (TyNeg (TyNeg TyTop)) "~~top"
    assertPrettyTy (TyNeg (TyUnion TyTop TyTop)) "~(top | top)"
    where
        assertPrettyTy t s = assertEqual s (showPretty t)

test_basicMinsem :: IO ()
test_basicMinsem = do
    printRepr M.impl TyTop
    printRepr M.impl TyBottom
    printRepr M.impl (TyAtom True)
    printRepr M.impl (TyAtom False)
    printRepr M.impl (TyProd (TyAtom False) (TyAtom True))
    printRepr M.impl (TyInter (TyAtom False) (TyNeg TyBottom))
    printRepr M.impl (TyUnion TyTop TyTop)
    printRepr M.impl (TyInter TyTop TyTop)
    printRepr M.impl (TyNeg TyTop)
    printRepr M.impl (TyInter TyTop (TyNeg TyTop))
    basicTests M.impl
