module Ty where

import Test.QuickCheck
import GHC.Generics
import Iface
import Pretty

data Ty =
    TyTop
    | TyBottom
    | TyAtom Bool
    | TyAnyAtom
    | TyAnyProd
    | TyProd Ty Ty
    | TyUnion Ty Ty
    | TyInter Ty Ty
    | TyDiff Ty Ty
    | TyNeg Ty
    deriving (Show, Read, Eq, Generic)

instance Arbitrary Ty where
    arbitrary = sized arbitraryTy
    shrink = genericShrink

instance Pretty Ty where
  pretty = prettyPrec 0

instance PrettyPrec Ty where
  prettyPrec prec t =
    case t of
      TyTop -> pretty "top"
      TyBottom -> pretty "bottom"
      TyAtom True -> pretty "True"
      TyAtom False -> pretty "False"
      TyAnyAtom -> pretty "atom"
      TyProd t1 t2 -> parens (pretty t1 <> comma <> pretty t2)
      TyAnyProd -> pretty "prod"
      TyUnion t1 t2 ->
        withParens prec 1 $
          (prettyPrec 2 t1) <>
          pretty "∨" <>
          (prettyPrec 2 t2)
      TyInter t1 t2 ->
        withParens prec 2 $
          (prettyPrec 3 t1) <>
          pretty "∧" <>
          (prettyPrec 3 t2)
      TyDiff t1 t2 ->
        withParens prec 2 $
          (prettyPrec 3 t1) <>
          pretty "\\" <>
          (prettyPrec 3 t2)
      TyNeg t ->
        withParens prec 3 $
          pretty "¬" <>
          prettyPrec 4 t

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
    | size <= 1 = frequency [(1, pure TyTop), (1, pure TyBottom), (1, pure TyAnyAtom),
                             (1, pure TyAnyProd)]
    | otherwise =
        frequency ([(12, pure (TyAtom True)), (12, pure (TyAtom False))] ++
                    (map (\f -> (10, arbitraryTyBinOp size f)) [TyProd, TyUnion, TyInter, TyDiff]) ++
                    [(10, arbitraryTyUnOp size TyNeg)])

tyRep :: Monad m => SemIface t s m -> Ty -> m t
tyRep impl t =
    case t of
      TyTop -> tyAny impl
      TyBottom -> tyEmpty impl
      TyAtom b -> tyAtom impl b
      TyAnyProd -> tyRep impl (TyProd TyTop TyTop)
      TyAnyAtom -> tyRep impl (TyDiff TyTop TyAnyProd)
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
      TyDiff t1 t2 -> tyRep impl (TyInter t1 (TyNeg t2))
      TyNeg t -> do
        t' <- tyRep impl t
        tyNeg impl t'
