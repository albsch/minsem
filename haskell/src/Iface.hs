module Iface (SemIface(..)) where

data SemIface t m =
    SemIface {
        tyAny :: m t,
        tyEmpty :: m t,
        tyAtom :: Bool -> m t,
        tyProd :: t -> t -> m t,
        tyUnion :: t -> t -> m t,
        tyIntersect :: t -> t -> m t,
        tyNeg :: t -> m t,
        isEmpty :: t -> m Bool
    }
