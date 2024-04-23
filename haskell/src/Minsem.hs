module Minsem where

import GHC.Generics
import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import qualified Control.Monad.State.Strict as S
import qualified Data.Foldable as F
import Utils
import Control.Monad
import qualified Data.List as L

data Flag = FlagTrue
    deriving (Eq, Generic)

instance Hashable Flag

data Prod = Prod { p_left :: Ty, p_right :: Ty }
    deriving (Eq, Generic)

instance Hashable Prod

newtype TyRef = TyRef { unTyRef :: Int }
    deriving (Eq, Hashable)

data Ty =
    IsTyRef TyRef
    | IsTyRec TyRec
    deriving (Eq, Generic)

instance Hashable Ty

data TyRec = TyRec { tr_flag :: Dnf Flag, tr_prod :: Dnf Prod }
    deriving (Eq, Generic)

instance Hashable TyRec

-- Dnf (disjunctive normale form) is the disjunction of a list of
-- Conj values. Conj is a conjunction of positive and negative literals.
-- An empty disjunction is equivalent to false.
-- An empty conjunction is equivalent to true.
newtype Dnf a = Dnf [Conj a]
    deriving (Eq, Hashable)

data Conj a = Conj { c_pos :: [a], c_neg :: [a] }
    deriving (Eq, Generic)

instance Hashable a => Hashable (Conj a)

flag :: Dnf Flag
flag = Dnf [Conj [FlagTrue] []]

negatedFlag :: Dnf Flag
negatedFlag = Dnf [Conj [] [FlagTrue]]

prod :: Prod -> Dnf Prod
prod p = Dnf [Conj [p] []]

prod' :: Ty -> Ty -> Dnf Prod
prod' a b = prod (Prod a b)

negatedProd :: Prod -> Dnf Prod
negatedProd p = Dnf [Conj [] [p]]

type TyMap = HashMap TyRef TyRec
data TyState = TyState { s_nextTyRef :: !Int, s_tyMap :: !TyMap }

newtype T a = T { unT :: S.State TyState a }
    deriving (Functor, Applicative, Monad, S.MonadState TyState)

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
    anyRec = TyRec flag (prod' tyAny tyAny)
    initTyMap = HashMap.fromList [(TyRef 0, anyRec)]

store :: TyRef -> TyRec -> T TyRef
store tyRef tyRec = do
    -- FIXME: not efficient: to check for structural equality with an existing type, we
    -- look at all types in the type state.
    state <- S.get
    let tyMap = s_tyMap state
    case L.lookup tyRec (map (\(x, y) -> (y, x)) (HashMap.toList tyMap)) of
        Just existingRef -> pure existingRef
        Nothing ->
            case HashMap.lookup tyRef tyMap of
                Just _ -> error ("Tried to store already stored TyRef")
                Nothing -> do
                    S.put $! state { s_tyMap = HashMap.insert tyRef tyRec tyMap }
                    pure tyRef

mkTyEmpty :: T Ty
mkTyEmpty = neg tyAny

neg :: Ty -> T Ty
neg (IsTyRec r) = do
    r' <- negTyRec r
    pure (IsTyRec r')
neg (IsTyRef r) = do
    ref <- corecRef r HashMap.empty (\r _ -> negTyRec r)
    pure (IsTyRef ref)

negTyRec :: TyRec -> T TyRec
negTyRec (TyRec f t) = do
    f' <- negFlag f
    t' <- negProd t
    pure $ TyRec f' t'
  where
    negFlag :: Dnf Flag -> T (Dnf Flag)
    negFlag f = dnf f processFlag intersectDnf
    processFlag :: Conj Flag -> T (Dnf Flag)
    processFlag conj =
        let (x:xs) =
                replicate (length (c_pos conj)) negatedFlag ++
                replicate (length (c_neg conj)) flag
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
    case HashMap.lookup tyRef (s_tyMap state) of
        Just t -> pure t
        Nothing -> error "unknown TyRef"

resolveTy :: Ty -> T TyRec
resolveTy (IsTyRec r) = pure r
resolveTy (IsTyRef r) = resolveTyRef r

corecRef :: TyRef -> Memo TyRef -> (TyRec -> Memo TyRef  -> T TyRec) -> T TyRef
corecRef ref memo f =
    case HashMap.lookup ref memo of
        Just v -> pure v
        Nothing -> do
            tyRef <- freshTyRef
            let newMemo = HashMap.insert ref tyRef memo
            ty <- resolveTyRef ref
            tyRec <- f ty newMemo
            store tyRef tyRec -- ?? might return a TyRef different from tyRef

corecConst :: TyRef -> Memo c -> (TyRec -> Memo c -> T c) -> c -> T c
corecConst ref memo f val =
    case HashMap.lookup ref memo of
        Just v -> pure v
        Nothing -> do
            ty <- resolveTyRef ref
            let newMemo = HashMap.insert ref val memo
            f ty newMemo

isEmpty :: Ty -> T Bool
isEmpty ty = isEmpty' ty HashMap.empty

isEmpty' :: Ty -> Memo Bool -> T Bool
isEmpty' (IsTyRec r) memo = tyRecIsEmpty r memo
isEmpty' (IsTyRef r) memo = corecConst r memo tyRecIsEmpty True

tyRecIsEmpty :: TyRec -> Memo Bool -> T Bool
tyRecIsEmpty (TyRec flags prods) memo = do
    b1 <- isEmptyFlags flags
    b2 <- isEmptyProds prods memo
    pure (b1 && b2)
    where
        isEmptyFlags :: Dnf Flag -> T Bool
        isEmptyFlags d = dnf d (\(Conj _ neg) -> pure (not (null neg))) (&&)
        isEmptyProds :: Dnf Prod -> Memo Bool -> T Bool
        isEmptyProds d memo = dnf d (processProd memo) (&&)
        processProd :: Memo Bool -> Conj Prod -> T Bool
        processProd memo (Conj pos neg) = do
            p <- bigIntersect pos
            phi p neg memo

intersect :: Ty -> Ty -> T Ty
intersect t1 t2 = do
    rec1 <- resolveTy t1
    rec2 <- resolveTy t2
    pure (IsTyRec (intersectTyRec rec1 rec2))

intersectTyRec :: TyRec -> TyRec -> TyRec
intersectTyRec (TyRec f1 p1) (TyRec f2 p2) =
    TyRec (intersectDnf f1 f2) (intersectDnf p1 p2)

union :: Ty -> Ty -> T Ty
union t1 t2 = do
    rec1 <- resolveTy t1
    rec2 <- resolveTy t2
    pure (IsTyRec (unionTyRec rec1 rec2))

unionTyRec :: TyRec -> TyRec -> TyRec
unionTyRec (TyRec f1 p1) (TyRec f2 p2) =
    TyRec (unionDnf f1 f2) (unionDnf p1 p2)


bigIntersect :: [Prod] -> T Prod
bigIntersect [] = pure (Prod tyAny tyAny)
bigIntersect [prod] = pure prod
bigIntersect (Prod t1 t2 : Prod t3 t4 : rest) = do
    tl <- intersect t1 t3
    tr <- intersect t2 t4
    bigIntersect (Prod tl tr : rest)

phi :: Prod -> [Prod] -> Memo Bool -> T Bool
phi p neg memo = do
    tyEmpty <- mkTyEmpty
    phi' p neg tyEmpty tyEmpty memo

phi' :: Prod -> [Prod] -> Ty -> Ty -> Memo Bool -> T Bool
phi' (Prod ts1 ts2) [] t1 t2 memo = do
    n1 <- neg t1
    l <- intersect ts1 n1
    res1 <- isEmpty' l memo
    n2 <- neg t2
    r <- intersect ts2 n2
    res2 <- isEmpty' r memo
    pure (res1 || res2)
phi' prod (Prod t1 t2 : rest) left right memo = do
    tl <- union left t1
    res1 <- phi' prod rest tl right memo
    tr <- union right t2
    res2 <- phi' prod rest left tr memo
    pure (res1 && res2)

someFunc :: IO ()
someFunc = putStrLn "someFunc"
