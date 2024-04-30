{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wwarn #-}
module Minsem (
    T,
    TyState,
    runT,
    Ty,
    impl
) where

import GHC.Generics
import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import qualified Control.Monad.State.Strict as S
import qualified Data.Foldable as F
import Utils
import Control.Monad
import qualified Data.List as L
import qualified Iface as I
import Pretty
import Trace

newtype Atom = Atom Bool
    deriving (Show, Eq, Hashable, Enum, Bounded)

instance Pretty Atom where
    pretty (Atom True) = pretty "T"
    pretty (Atom False) = pretty "F"

data Prod = Prod { p_left :: Ty, p_right :: Ty }
    deriving (Show, Eq, Generic)

instance Hashable Prod

instance Pretty Prod where
    pretty (Prod l r) =
        parens (pretty l <> comma <+> pretty r)

newtype TyRef = TyRef { _unTyRef :: Int }
    deriving (Show, Eq, Hashable, Ord)

instance Pretty TyRef where
    pretty (TyRef i) = pretty i

data Ty =
    IsTyRef TyRef
    | IsTyRec TyRec
    deriving (Show, Eq, Generic)

instance Hashable Ty

instance Pretty Ty where
    pretty (IsTyRef r) = pretty r
    pretty (IsTyRec r) = pretty r

data TyRec = TyRec { tr_atom :: Dnf Atom, tr_prod :: Dnf Prod }
    deriving (Show, Eq, Generic)

instance Hashable TyRec

instance Pretty TyRec where
    pretty (TyRec a p) =
        braces (pretty "atom=" <> (pretty a) <> pretty ", prod=" <> pretty p)

-- Dnf (disjunctive normale form) is the disjunction of a list of
-- Conj values. Conj is a conjunction of positive and negative literals.
-- An empty disjunction is equivalent to false.
-- An empty conjunction is equivalent to true.
newtype Dnf a = Dnf [Conj a]
    deriving (Show, Eq, Hashable)

instance Pretty a => Pretty (Dnf a) where
    pretty (Dnf []) = pretty "∨"
    pretty (Dnf conjs) = hcat $ punctuate (pretty " ∨ ") (map pretty conjs)

data Conj a = Conj { c_pos :: [a], c_neg :: [a] }
    deriving (Show, Eq, Generic)

instance Hashable a => Hashable (Conj a)

instance Pretty a => Pretty (Conj a) where
    pretty (Conj p n) =
        hcat $ punctuate (pretty " ∧ ") $
          map pretty p ++ map (\x -> pretty "¬" <> pretty x) n

atom :: Atom -> Dnf Atom
atom a = Dnf [Conj [a] []]

negatedAtom :: Atom -> Dnf Atom
negatedAtom a = Dnf [Conj [] [a]]

anyAtom :: Dnf Atom
anyAtom = Dnf [Conj [Atom True] [], Conj [Atom False] []]

prod :: Prod -> Dnf Prod
prod p = Dnf [Conj [p] []]

prod' :: Ty -> Ty -> Dnf Prod
prod' a b = prod (Prod a b)

negatedProd :: Prod -> Dnf Prod
negatedProd p = Dnf [Conj [] [p]]

tyAtom :: Bool -> Ty
tyAtom b = IsTyRec (TyRec (atom (Atom b)) (Dnf []))

tyProd :: Ty -> Ty -> Ty
tyProd t1 t2 = IsTyRec (TyRec (Dnf []) (prod' t1 t2))

newtype TyMap = TyMap { unTyMap :: HashMap TyRef TyRec }
    deriving (Show)

instance Pretty TyMap where
    pretty (TyMap m) =
        let l = L.sortOn fst (HashMap.toList m)
        in vcat $ map (\(k, v) -> pretty k <+> pretty "➔" <+> pretty v) l

data TyState = TyState { s_nextTyRef :: !Int, s_tyMap :: !TyMap }
    deriving (Show)

instance Pretty TyState where
    pretty (TyState _ m) = pretty m

newtype T a = T { _unT :: S.State TyState a }
    deriving (Functor, Applicative, Monad, S.MonadState TyState)

runT :: T a -> (a, TyState)
runT (T x) = S.runState x initTyState

freshTyRef :: T TyRef
freshTyRef = do
    state <- S.get
    let i = s_nextTyRef state
    S.put $! state { s_nextTyRef = i + 1 }
    pure (TyRef i)

tyAny :: Ty
tyAny = IsTyRef (TyRef 0)

initTyState :: TyState
initTyState = TyState 1 initTyMap
  where
    anyRec = TyRec anyAtom (prod' tyAny tyAny)
    initTyMap = TyMap (HashMap.fromList [(TyRef 0, anyRec)])

store :: TyRef -> TyRec -> T TyRef
store tyRef tyRec = do
    -- FIXME: not efficient: to check for structural equality with an existing type, we
    -- look at all types in the type state.
    state <- S.get
    let TyMap tyMap = s_tyMap state
    case L.lookup tyRec (map (\(x, y) -> (y, x)) (HashMap.toList tyMap)) of
        Just existingRef -> pure existingRef
        Nothing ->
            case HashMap.lookup tyRef tyMap of
                Just _ -> error ("Tried to store already stored TyRef")
                Nothing -> do
                    S.put $! state { s_tyMap = TyMap (HashMap.insert tyRef tyRec tyMap) }
                    pure tyRef

tyEmpty :: T Ty
tyEmpty = tyNeg tyAny

tyNeg :: Ty -> T Ty
tyNeg (IsTyRec r) = do
    r' <- negTyRec r
    pure (IsTyRec r')
tyNeg (IsTyRef r) = do
    ref <- corecRef r HashMap.empty (\r _ -> negTyRec r)
    pure (IsTyRef ref)

negTyRec :: TyRec -> T TyRec
negTyRec (TyRec f t) = do
    f' <- negAtom f
    t' <- negProd t
    pure $ TyRec f' t'
  where
    negAtom :: Dnf Atom -> T (Dnf Atom)
    negAtom f = dnf f processAtom intersectDnf
    processAtom :: Conj Atom -> T (Dnf Atom)
    processAtom conj =
        let (x:xs) =
                [negatedAtom t | t <- c_pos conj] ++
                [atom t | t <- c_neg conj]
        in pure (F.foldl' unionDnf x xs)
    negProd :: Dnf Prod -> T (Dnf Prod)
    negProd p = dnf p processProd intersectDnf
    processProd :: Conj Prod -> T (Dnf Prod)
    processProd conj =
        let (x:xs) =
                [negatedProd t | t <- c_pos conj] ++
                [prod t | t <- c_neg conj]
        in pure (F.foldl' unionDnf x xs)

dnf :: Dnf a -> (Conj a -> T b) -> (b -> b -> b) -> T b
dnf (Dnf (x:xs)) f c = do
    start <- f x
    foldM (\b a -> f a >>= \x -> pure (c b x)) start xs
dnf (Dnf []) _ _ = error "empty DNF"

unionDnf :: Hashable a => Dnf a -> Dnf a -> Dnf a
unionDnf (Dnf l1) (Dnf l2) =
    Dnf (nubHash (l1 ++ l2))

intersectDnf :: Hashable a => Dnf a -> Dnf a -> Dnf a
intersectDnf (Dnf l1) (Dnf l2) =
    Dnf [Conj (nubHash (pos1 ++ pos2)) (nubHash (neg1 ++ neg2))
            | Conj pos1 neg1 <- l1, Conj pos2 neg2 <- l2]

type Memo v = HashMap TyRef v

resolveTyRef :: TyRef -> T TyRec
resolveTyRef tyRef = do
    state <- S.get
    case HashMap.lookup tyRef (unTyMap (s_tyMap state)) of
        Just t -> pure t
        Nothing -> error "unknown TyRef"

corecRef :: TyRef -> Memo TyRef -> (TyRec -> Memo TyRef  -> T TyRec) -> T TyRef
corecRef ref memo f = trace "corecRef" $
    case HashMap.lookup ref memo of
        Just v -> pure v
        Nothing -> do
            tyRef <- freshTyRef
            let newMemo = HashMap.insert ref tyRef memo
            ty <- resolveTyRef ref
            tyRec <- f ty newMemo
            store tyRef tyRec -- ?? might return a TyRef different from tyRef

class Hashable r => Resolvable r where
    type Resolved r
    resolve :: r -> T (Resolved r)

instance Resolvable TyRef where
    type Resolved TyRef = TyRec
    resolve = resolveTyRef

instance (Resolvable r1, Resolvable r2) => Resolvable (r1, r2) where
    type Resolved (r1, r2) = (Resolved r1, Resolved r2)
    resolve (r1, r2) = do
        x1 <- resolve r1
        x2 <- resolve r2
        pure (x1, x2)

type Memo' r v = HashMap r v

corecRef' :: Resolvable r => r -> Memo' r TyRef -> (Resolved r -> Memo' r TyRef  -> T TyRec) -> T TyRef
corecRef' ref memo f = trace "corecRef'" $
    case HashMap.lookup ref memo of
        Just v -> pure v
        Nothing -> do
            tyRef <- freshTyRef
            let newMemo = HashMap.insert ref tyRef memo
            ty <- resolve ref
            tyRec <- f ty newMemo
            store tyRef tyRec -- ?? might return a TyRef different from tyRef

corecConst :: TyRef -> Memo c -> (TyRec -> Memo c -> T c) -> c -> T c
corecConst ref memo f val = trace ("corecConst, ref=" ++ showPretty ref) $
    case HashMap.lookup ref memo of
        Just v -> trace ("memo good") $ pure v
        Nothing -> do
            ty <- resolveTyRef ref
            let newMemo = HashMap.insert ref val memo
            f ty newMemo

isEmpty :: Ty -> T Bool
isEmpty ty = trace "isEmpty" $ isEmpty' ty HashMap.empty

isEmpty' :: Ty -> Memo Bool -> T Bool
isEmpty' t memo = trace ("isEmpty' " ++ showPretty t ++ ", memo: " ++ show memo) $
    case t of
        IsTyRec r -> tyRecIsEmpty r memo
        IsTyRef r -> corecConst r memo tyRecIsEmpty True

tyRecIsEmpty :: TyRec -> Memo Bool -> T Bool
tyRecIsEmpty t@(TyRec atoms prods) memo = trace ("tyRecIsEmpty " ++ showPretty t) $ do
    b1 <- isEmptyAtoms atoms
    b2 <- isEmptyProds prods memo
    pure (b1 && b2)
    where
        isEmptyAtoms :: Dnf Atom -> T Bool
        isEmptyAtoms d = dnf d (\(Conj _ neg) -> pure (not (null neg))) (&&)
        isEmptyProds :: Dnf Prod -> Memo Bool -> T Bool
        isEmptyProds d memo = dnf d (processProd memo) (&&)
        processProd :: Memo Bool -> Conj Prod -> T Bool
        processProd memo (Conj pos neg) = do
            p <- bigIntersect pos
            phi p neg memo

corecBinOp :: (TyRec -> TyRec -> TyRec) -> Ty -> Ty -> T Ty
corecBinOp f (IsTyRec rec1) (IsTyRec rec2) = do
    pure (IsTyRec (f rec1 rec2))
corecBinOp f t1 t2 = do
    ref1 <- mkRef t1
    ref2 <- mkRef t2
    resRef <- corecRef' (ref1, ref2) HashMap.empty $
        \(rec1, rec2) _ -> pure (f rec1 rec2)
    pure (IsTyRef resRef)
    where
        mkRef (IsTyRef r) = pure r
        mkRef (IsTyRec r) = do
            ref <- freshTyRef
            store ref r

tyIntersect :: Ty -> Ty -> T Ty
tyIntersect = corecBinOp intersectTyRec
    where
        intersectTyRec :: TyRec -> TyRec -> TyRec
        intersectTyRec (TyRec f1 p1) (TyRec f2 p2) =
            TyRec (intersectDnf f1 f2) (intersectDnf p1 p2)

tyUnion :: Ty -> Ty -> T Ty
tyUnion = corecBinOp unionTyRec
    where
        unionTyRec :: TyRec -> TyRec -> TyRec
        unionTyRec (TyRec f1 p1) (TyRec f2 p2) =
            TyRec (unionDnf f1 f2) (unionDnf p1 p2)


bigIntersect :: [Prod] -> T Prod
bigIntersect [] = pure (Prod tyAny tyAny)
bigIntersect [prod] = pure prod
bigIntersect (Prod t1 t2 : Prod t3 t4 : rest) = do
    tl <- tyIntersect t1 t3
    tr <- tyIntersect t2 t4
    bigIntersect (Prod tl tr : rest)

phi :: Prod -> [Prod] -> Memo Bool -> T Bool
phi p neg memo = do
    e <- tyEmpty
    phi' p neg e e memo

phi' :: Prod -> [Prod] -> Ty -> Ty -> Memo Bool -> T Bool
phi' (Prod ts1 ts2) [] t1 t2 memo = do
    n1 <- tyNeg t1
    l <- tyIntersect ts1 n1
    res1 <- isEmpty' l memo
    n2 <- tyNeg t2
    r <- tyIntersect ts2 n2
    res2 <- isEmpty' r memo
    pure (res1 || res2)
phi' prod (Prod t1 t2 : rest) left right memo = do
    tl <- tyUnion left t1
    res1 <- phi' prod rest tl right memo
    tr <- tyUnion right t2
    res2 <- phi' prod rest left tr memo
    pure (res1 && res2)

impl :: I.SemIface Ty TyState T
impl =
    I.SemIface {
        I.tyAny = pure tyAny,
        I.tyEmpty = tyEmpty,
        I.tyAtom = \b -> pure (tyAtom b),
        I.tyProd = \t1 t2 -> pure (tyProd t1 t2),
        I.tyUnion = tyUnion,
        I.tyIntersect = tyIntersect,
        I.tyNeg = tyNeg,
        I.isEmpty = isEmpty,
        I.run = runT
    }
