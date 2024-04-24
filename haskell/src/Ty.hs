module Ty where

import Test.QuickCheck
import GHC.Generics
import Iface

data Ty =
    TyTop
    | TyBottom
    | TyAtom Bool
    | TyProd Ty Ty
    | TyUnion Ty Ty
    | TyInter Ty Ty
    | TyNeg Ty
    deriving (Eq, Generic)

instance Arbitrary Ty where
    arbitrary = sized arbitraryTy
    shrink = genericShrink

arbitraryTyBinOp :: Int -> (Ty -> Ty -> Ty) -> Gen Ty
arbitraryTyBinOp size f = do
    l <- arbitraryTy (size `div` 2)
    r <- arbitraryTy (size `div` 2)
    pure (f l r)

arbitraryTyUnOp :: Int -> (Ty -> Ty) -> Gen Ty
arbitraryTyUnOp size f = do
    ty <- arbitraryTy (size `div` 2)
    pure (f ty)

arbitraryTy :: Int -> Gen Ty
arbitraryTy size
    | size <= 1 = frequency [(1, pure TyTop), (1, pure TyBottom)]
    | otherwise =
        frequency ([(12, pure (TyAtom True)), (12, pure (TyAtom False))] ++
                    (map (\f -> (10, arbitraryTyBinOp size f)) [TyProd, TyUnion, TyInter]) ++
                    [(10, arbitraryTyUnOp size TyNeg)])

tyRep :: Monad m => SemIface t m -> Ty -> m t
tyRep impl t =
    case t of
      TyTop -> tyAny impl
      TyBottom -> tyEmpty impl
      TyAtom b -> tyAtom impl b
      TyProd t1 t2 -> do
        t1' <- tyRep impl t1
        t2' <- tyRep impl t2
        tyProd impl t1' t2'
      TyUnion t1 t2 -> do
        t1' <- tyRep impl t1
        t2' <- tyRep impl t2
        tyUnion impl t1' t2'
      TyInter t1 t2 -> do
        t1' <- tyRep impl t1
        t2' <- tyRep impl t2
        tyIntersect impl t1' t2'
      TyNeg t -> do
        t' <- tyRep impl t
        tyNeg impl t'
