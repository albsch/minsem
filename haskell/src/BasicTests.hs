module BasicTests where

import Ty
import Iface
import qualified Minsem as M
import Pretty
import Control.Monad
import System.Timeout
import Control.Exception (evaluate)

assertTrue :: Bool -> IO ()
assertTrue True = pure ()
assertTrue False = error "expected True given False"

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
    x <- timeout subTyTimeout $ evaluate (run impl (isSubTy impl t1 t2))
    case x of
        Nothing ->
            fail ("Subtype checked timed out.")
        Just ((res, t), s) ->
            when (b /= res) $
                fail ("Expected " ++ show b ++ " got " ++ show res ++ "\nInternal type: " ++
                      showPretty t ++ "\n" ++ show (indent 2 (pretty s)))

basicTests :: (Pretty t, Pretty s, Monad m) => SemIface t s m -> IO ()
basicTests impl = do
    assertSubTy impl TyTop TyTop True
    assertSubTy impl TyTop TyBottom False
    assertSubTy impl TyBottom TyTop True

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
    printRepr M.impl (TyUnion TyTop TyTop)
    printRepr M.impl (TyInter TyTop TyTop)
    printRepr M.impl (TyNeg TyTop)
    printRepr M.impl (TyInter TyTop (TyNeg TyTop))
    basicTests M.impl
