{-# LANGUAGE
  RankNTypes,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  ViewPatterns,
  ParallelListComp,
  ScopedTypeVariables,
  NoMonomorphismRestriction,
  NoMonoPatBinds #-}
module PalkaGenerator where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans (lift, MonadTrans)
import Control.Parallel.Strategies

import Data.Char (isAlphaNum)
import qualified Data.Foldable as F
import Data.Foldable (Foldable, foldMap)
import Data.List (nub, sort, sortBy, intersperse, intercalate, (\\), foldl', group, groupBy)
import Data.Maybe
import Data.Monoid
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Traversable as T
import Data.Traversable (Traversable, traverse)

import System.CPUTime
import System.Exit
import System.IO
import System.IO.Unsafe
import System.Process

import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Monadic
import Test.QuickCheck.Property hiding (Result (..))
import qualified Test.QuickCheck.Property as Prop
import Test.QuickCheck.State
import Test.QuickCheck.Text

import Text.Show


--impossibleCase :: (forall a. a) -> (forall a. a)
impossibleCase = error "impossible case"

newtype Name = Name String
  deriving (Eq, Ord)

instance Show Name where
  show (Name s) = s

-- Let's say we allow alphanum characters here and '_'
instance Read Name where
  readsPrec _ s = case n of
    "" -> []
    _  -> [(Name n, rest)]
    where
    (n, rest) = span (\x -> isAlphaNum x || x == '_') s

data Type v = TVar v | TCon Int Name | TApp (Type v) (Type v)
  deriving (Eq, Ord, Show, Read)

infixr 5 -->

t1 --> t2 = TApp (TApp (TCon 2 (Name "->")) t1) t2

tcon n s = TCon n (Name s)

data AType v = ATArr (Type v) (Type v)

aType :: Type v -> Maybe (AType v)
aType (TApp (TApp (TCon 2 (Name "->")) a) b)
        = Just (ATArr a b)
aType _ = Nothing

typeSize (TVar _)   = 1
typeSize (TCon _ _) = 1
typeSize (TApp a b) = typeSize a + typeSize b + 1

tYPESize (TYPE (POLY n p)) = typeSize (p [0..n - 1])

bracket s = "(" ++ s ++ ")"

unparseType (TVar x)   = show x
unparseType (TCon _ c) = show c
unparseType (aType -> Just (ATArr a b))
                       = b1 (unparseType a) ++ " -> " ++ unparseType b
  where
  b1 = case a of
    TApp _  _ -> bracket
    _         -> id
unparseType (TApp a b) = b1 (unparseType a) ++ " " ++ b2 (unparseType b)
  where
  b1 = case a of
    TApp _ _ -> bracket
    _        -> id
  b2 = case b of
    TApp _ _ -> bracket
    _        -> id

instance Functor Type where
  fmap f (TVar v)     = TVar $ f v
  fmap f (TCon n s)   = TCon n s
  fmap f (TApp t1 t2) = TApp (fmap f t1) (fmap f t2)

instance Applicative Type where 
    pure = return
    (<*>) = ap

instance Monad Type where
  t >>= f = tSubst $ fmap f t
  return  = TVar

tSubst :: Type (Type v) -> Type v
tSubst (TVar v)     = v
tSubst (TCon n s)   = TCon n s
tSubst (TApp t1 t2) = TApp (tSubst t1) (tSubst t2)

instance Foldable Type where
  foldMap f (TVar v)     = f v
  foldMap f (TCon _ _)   = mempty
  foldMap f (TApp t1 t2) = foldMap f t1 `mappend` foldMap f t2

instance Traversable Type where
  traverse f (TVar v)     = TVar <$> f v
  traverse f (TCon n s)   = pure $ TCon n s
  traverse f (TApp t1 t2) = TApp <$> traverse f t1 <*> traverse f t2

tOccurs m t = getAny $ foldMap (Any . (== m)) t
--tOccurs m (TVar v) = m == v
--tOccurs _ (TCon _ _) = False
--tOccurs m (TApp a b) = tOccurs m a || tOccurs m b

data FrBd a b = Free a | Bound b
  deriving (Show, Eq, Ord)

instance Functor (FrBd a) where
  fmap f (Bound b) = Bound $ f b
  fmap _ (Free x)  = Free x

frbd f _ (Free x)  = f x
frbd _ g (Bound y) = g y

-- Close over environment
data Close t v = Close Int ([v] -> t v)
unClose (Close _ p) = p

newtype CLOSE t = CLOSE (forall v. Close t v)
-- Insert type lambdas in the front
-- change representation into Int indices?
data POLY t w = POLY Int (forall v. [v] -> t (FrBd w v))

-- Polytype
newtype TYPE v = TYPE (POLY Type v)

-- Polytype closed over env
newtype PTYPE = PTYPE (forall v. Close TYPE v)
-- Monotype closed over env
newtype MTYPE = MTYPE (forall v. Close Type v)

instance Eq v => Eq (TYPE v) where
  (TYPE (POLY n f)) == (TYPE (POLY m g))
    | n == m    = f [0..n-1] == g [0..n-1]
    | otherwise = False

instance Ord v => Ord (TYPE v) where
  compare (TYPE (POLY n f)) (TYPE (POLY m g))
    | n == m    = compare (f [0..n-1]) (g [0..n-1])
    | otherwise = compare n m

instance Show v => Show (TYPE v) where
  show (TYPE (POLY m g)) =
    "TYPE " ++ show m ++ " (" ++ show (g bound) ++ ")"
    where
    bound = take m [Name [x] | x <- ['a'..]]

unparseTYPE (TYPE (POLY m g)) =
  "TYPE " ++ show m ++ " (" ++ unparseType (g bound) ++ ")"
  where
  bound = take m [Name [x] | x <- ['a'..]]

instance Functor TYPE where
  fmap f (TYPE (POLY n g)) =
    TYPE (POLY n (\v -> fmap (frbd (Free . f) Bound) $ g v))

instance Show MTYPE where
  show (MTYPE c) =
    "MTYPE " ++ show n ++ " (" ++ show (f fromEnv) ++ ")"
    where
    (Close n f) = c
    fromEnv     = take n [Name [x] | x <- ['a'..]]

tApply' :: TYPE v -> [Type v] -> Type v
tApply' (TYPE (POLY m t)) a = f
  where
  f | l /= m    = error "tApply: arg number mismatch"
    | otherwise =
        do
          x <- t a
          let bf (Bound b) = b
              bf (Free f)  = TVar f
          bf x
    where
    l = length a

-- Need substitutions
-- Need opening operation (maybe a monad?)
-- open :: TYPE v -> (Type v -> m a) -> m a
-- what about 'rigid' variables?
-- also, some variables might be not rigid, but still shared!!!

-- Annotate variables
data Annot a v = Annot a v
  deriving (Show)

unAnnot (Annot _ v) = v

instance Eq a => Eq (Annot a v) where
  (Annot n1 _) == (Annot n2 _) = n1 == n2

instance Ord a => Ord (Annot a v) where
  compare (Annot n1 _) (Annot n2 _) = compare n1 n2

-- maybe we should do away w/o TYPE and have all the types in the environment
unify :: Eq v => TYPE v -> TYPE v ->
          Maybe ([Maybe (Type (FrBd v Int))], [Maybe (Type (FrBd v Int))])
unify (TYPE (POLY m1 t1)) (TYPE (POLY m2 t2)) =
  solve [(t1 [0..m1-1], t2 [m1..m1+m2-1])] []
  where
  solve [] l = return
      (map (\m -> lookup m l') [0..m1-1],
       map (\m -> lookup m l') [m1..m1+m2-1])
    where l' = l ++ revRefs l
  solve (((TVar (Free x)), (TVar (Free y))):xs) l
    | x == y    = solve xs l
    | otherwise = Nothing
  solve (((TVar (Bound nx)), y):xs) l = elim nx y xs l
  solve ((x, (TVar (Bound ny))):xs) l = elim ny x xs l
  solve ((((TCon n c), (TCon n' c'))):xs) l
    | n == n' && c == c' = solve xs l
    | otherwise          = Nothing
  solve (((TApp a b), (TApp c d)):xs) l = solve ((a, c):(b, d):xs) l
  solve _ _ = Nothing
  elim nx y xs l -- this recurses further into solve
    | tOccurs (Bound nx) y = Nothing
    | otherwise            = do
      solve
        (map (\(a, b) -> (mySubst nx y a, mySubst nx y b)) xs)
        ((nx, y):(map (\(m, b) -> (m, mySubst nx y b)) l))
  mySubst m t t' = t' >>= aux
    where
    aux v@(Bound m')
      | m == m'   = t
      | otherwise = TVar v
    aux v = TVar v
  revRefs l = [ (ny, (TVar (Bound nx))) | (nx, (TVar (Bound ny))) <- l]

{- Free variables are 'rigid', bound variables participate in the substitution.
 - Some bound variables might be missing from the substitution if their mapping
 - is trivial.
 -}
-- how about unify as unification of constraints?
unify' :: (Eq v, Eq w) => Type (FrBd v w) -> Type (FrBd v w) ->
          Maybe [(w, Type (FrBd v w))]
unify' t1 t2 = solve [(t1, t2)] []
  where
  solve [] l = return $ l
  solve ((TVar (Free x), TVar (Free y)):xs) l
    | x == y    = solve xs l
    | otherwise = Nothing
  solve ((x@(TVar (Bound nx)), y):xs) l
    | x == y    = solve xs l
    | otherwise = elim nx y xs l
  solve ((x, TVar (Bound ny)):xs) l = elim ny x xs l
  solve ((TCon n c, TCon n' c'):xs) l
    | n == n' && c == c' = solve xs l
    | otherwise          = Nothing
  solve ((TApp a b, TApp c d):xs) l = solve ((a, c):(b, d):xs) l
  solve _ _ = Nothing
  elim nx y xs l -- this recurses further into solve
    | tOccurs (Bound nx) y = Nothing
    | otherwise            = do
      solve
        (map (\(a, b) -> (mySubst nx y a, mySubst nx y b)) xs)
        ((nx, y):(map (\(m, b) -> (m, mySubst nx y b)) l))
  mySubst m t t' = t' >>= aux
    where
    aux v@(Bound m')
      | m == m'   = t
      | otherwise = TVar v
    aux v = TVar v

--let CLOSE p = unify (CLOSE (Close 3 (\[a, b, c] -> UnifyArg (TVar a) (TVar b)))) in let (Close n _) = p in (unClose p [0..5])

testPType1 int bool = TYPE (POLY 2 $ \[a, b] ->
  (TApp (tcon 1 "[]") (TVar (Bound a)) --> (TVar (Bound b))) --> (TVar (Free int)))
testPType2 int bool = TYPE (POLY 0 $ \[] -> TApp (tcon 1 "[]") (TVar (Free int)))

testPType3 int bool = TYPE (POLY 2 $ \[a, b] ->
  TVar (Bound a) --> ((TVar (Bound b)) --> (TVar (Free int))))
testPType4 int bool = TYPE (POLY 2 $ \[a, b] ->
  TVar (Bound a) --> (TVar (Bound a)))

listType x = TApp (tcon 1 "[]") x

monadType x = TApp (tcon 1 "M") x

mapType = TYPE (POLY 2 $ \[a, b] ->
  (TVar (Bound a) --> (TVar (Bound b))) -->
    listType (TVar (Bound a)) --> listType (TVar (Bound b)))

idType = TYPE (POLY 1 $ \[a] -> TVar (Bound a) --> (TVar (Bound a)))

-- Type applications in Var: all variables bound in TYPE must be used,
-- otherwise we wouldn't know what to apply
-- how to turn a bound var into a free var?
data Term v w w' = Lam (Type v) (w -> Term v w w') | App (Term v w w') (Term v w w') | Var w'

instance (Show v, Show s) => Show (Term v Char s) where
  show t = aux ['a'..] t
    where
    aux l      (App t1 t2) =
      "App (" ++ aux l t1 ++ ") (" ++ aux l t2 ++ ")"
    aux (x:xs) (Lam t b)   =
      "Lam " ++ [x] ++ " (" ++ show t ++ ") (" ++ aux xs (b x) ++ ")"
    aux _      (Var w)     = "Var (" ++ show w ++ ")"
  
{-instance (Show v, Show s1, Show s2) => Show (Term v Char (FrBd s1 s2)) where
  show t = aux ['a'..] t
    where
    aux l      (App t1 t2) = "App (" ++ aux l t1 ++ ") (" ++ aux l t2 ++ ")"
    aux (x:xs) (Lam t b)   = "Lam " ++ [x] ++ " (" ++ show t ++ ") (" ++ aux xs (b x) ++ ")"
    aux _      (Var (Free x))   = "Var (" ++ show x ++ ")"
    aux _      (Var (Bound y))   = "Var (" ++ show y ++ ")"
-}

unparseTerm t = aux ['a'..] t
  where
  aux l      (App t1 t2) =
    b1 (aux l t1) ++ " " ++ b2 (aux l t2)
    where
    b1 = case t1 of
      (Lam _ _) -> bracket
      _         -> id
    b2 = case t2 of
      (Var _) -> id
      _         -> bracket
  aux (x:xs) (Lam t b) =
    "\\" ++ [x] ++ ":" ++ show t ++ ". " ++ aux xs (b x)
  aux _      (Var w)   = [w]
  --aux _      (Var w (Just a)) = [w] ++ "@" ++ show a

termSize (App t1 t2) = termSize t1 + termSize t2 + 1
termSize (Lam _ tf)  = termSize (tf ()) + 1
termSize _           = 1

data CTerm v = CTerm [TYPE v]
                     (forall w w'. [w'] -> Term v w (FrBd (w', [Type v]) w))

instance Show v => Show (CTerm v) where
  show (CTerm envt f) =
      "CTerm " ++ show (zip envVars envt) ++ " " ++
      show (f envVars :: Term v Char (FrBd (Char, [Type v]) Char))
    where
    l = length envt
    envVars = take l ['A'..]

cTermSize (CTerm e tf) = termSize (tf $ map (const ()) e)

newtype TERM = TERM (forall v. Close CTerm v)

mapTerm :: (w -> w1) -> (w1' -> w') -> Term t w1 w1' -> Term t w w'
mapTerm f g (Lam t ft)  = Lam t (\x -> mapTerm f g $ ft $ f x)
mapTerm f g (App t1 t2) = App (mapTerm f g t1) (mapTerm f g t2)
mapTerm f g (Var x)     = Var (g x)

mapFree :: (w -> w') -> Term t w1 (FrBd w w1') -> Term t w1 (FrBd w' w1')
mapFree f = mapTerm id (frbd (Free . f) Bound)

joinFree :: Term t w1 (FrBd (Term t w1 (FrBd w w1')) w1') -> Term t w1 (FrBd w w1')
joinFree (Lam t ft)      = Lam t (\x -> joinFree $ ft x)
joinFree (App t1 t2)     = App (joinFree t1) (joinFree t2)
joinFree (Var (Free x))  = x
joinFree (Var (Bound y)) = (Var (Bound y))

boundToFree :: (forall w1. w1 -> Term v w1 (FrBd w' w1)) -> w' -> Term v w (FrBd w' w)
boundToFree f v = mapTerm Just aux $ f Nothing
  where
  --transformed :: Maybe w -> Term v w (FrBd w' (Maybe w))
  --transformed v' = mapTerm Just id $ f v'
  aux (Free x)         = (Free x)
  aux (Bound Nothing)  = (Free v)
  aux (Bound (Just y)) = Bound y

freeVars :: Term v () (FrBd w' ()) -> [w']
freeVars (Lam _ f)       = freeVars $ f ()
freeVars (App a b)       = freeVars a ++ freeVars b
freeVars (Var (Free x))  = [x]
freeVars (Var (Bound x)) = []

freeVars' :: w -> Term v w (FrBd () w) -> [w]
freeVars' p (Lam _ f)       = freeVars' p $ f p
freeVars' p (App a b)       = freeVars' p a ++ freeVars' p b
freeVars' p (Var (Free x))  = []
freeVars' p (Var (Bound x)) = [x]

termWF' :: Eq v => Term v (Type v) (FrBd (TYPE v, [Type v]) (Type v)) -> Maybe (Type v)
termWF' f = aux f
  where
  aux (Lam lt f) = do
    rt <- aux (f lt)
    return $ lt --> rt
  aux (App a b) = do
    ta <- aux a
    tb <- aux b
    (ATArr ta1 ta2) <- aType ta
    if ta1 == tb
      then return ta2
      else Nothing
  aux (Var (Free (x, l))) = return (tApply' x l)
  aux (Var (Bound b))     = return b

termWF's :: Eq v => Term v (Type v) (Type v) -> Maybe (Type v)
termWF's f = aux f
  where
  aux (Lam lt f) = do
    rt <- aux (f lt)
    return $ lt --> rt
  aux (App a b)  = do
    ta <- aux a
    tb <- aux b
    (ATArr ta1 ta2) <- aType ta
    if ta1 == tb
      then return ta2
      else Nothing
  aux (Var x)    = return x

-- We can have some holes instead of variables
termWF'm :: Eq v =>
  Term v (Type v) (Maybe (FrBd (Type v) (Type v))) -> Maybe (Type v)
termWF'm f = aux f
  where
  aux (Lam lt f) = do
    rt <- aux (f lt)
    return $ lt --> rt
  aux (App a b)  = do
    ta <- aux a
    tb <- aux b
    (ATArr ta1 ta2) <- aType ta
    if ta1 == tb
      then return ta2
      else Nothing
  aux (Var (Just (Free x)))  = return x
  aux (Var (Just (Bound b))) = return b
  aux (Var _               ) = Nothing

-- remove universal type and turn it into an Annot?
termWF :: Eq v => CTerm v -> Maybe (Type v)
termWF (CTerm t f) = aux v
  where
  v = f t
  aux (Lam lt f) = do
    rt <- aux (f lt)
    return $ lt --> rt
  aux (App a b) = do
    ta <- aux a
    tb <- aux b
    (ATArr ta1 ta2) <- aType ta
    if ta1 == tb
      then return ta2
      else Nothing
  aux (Var (Free (x, l))) =
    return (tApply' x l)
  aux (Var (Bound b))     =
    return b
  --aux (Var _        )     = Nothing

-- Remove any unused bound variables, or return Nothing if all are used
normalizeTYPE :: TYPE v -> Maybe (TYPE v)
normalizeTYPE (TYPE (POLY n p))
  | lbv == n  = Nothing
  | otherwise = Just (TYPE (POLY lbv f))
  where
  bv = getBoundVars (p [Annot x x | x <- [0..n-1]])
  lbv = length bv
  f vars
    | length vars /= lbv =
      error "wrong number of vars: normalizeTYPE"
    | otherwise          =
      p $ expander (sort $ map unAnnot bv) [0..n-1] vars
  expander _         []     _    = []
  expander []        (a:ax) []   = undefined : expander [] ax []
  expander rr@(r:rx) (a:ax) vv@(v:vx)
    | r == a    = v : expander rx ax vx
    | otherwise = undefined : expander rr ax vv

getBoundVars :: Eq v => (Type (FrBd w v)) -> [v]
getBoundVars t = nub $ aux t
  where
  aux (TVar (Free _))  = []
  aux (TVar (Bound x)) = [x]
  aux (TCon _ _)       = []
  aux (TApp a b)       = aux a ++ aux b

-- if the type is normalized then we don't need the nested maybe
exactMatch :: Eq v => TYPE v -> Type v -> Maybe [Maybe (Type v)]
exactMatch (TYPE (POLY n p)) t = do
  targs <- aux (p [0..n-1]) t
  return $ map (\k -> IM.lookup k targs) [0..n-1]
  where
  aux (TVar (Bound n)) t = Just $ IM.singleton n t
  aux s@(TVar (Free v)) t
    | s == (fmap Free t) = Just $ IM.empty
    | otherwise = Nothing
  aux s@(TCon _ _) t
    | s == (fmap Free t) = Just $ IM.empty
    | otherwise = Nothing
  aux (TApp t1 t2) (TApp u1 u2) =
    aux t1 u1 >>= \r1 -> aux t2 u2 >>= \r2 -> merge r1 r2
  aux _ _ = Nothing
  merge c1 c2 =
    case IM.minViewWithKey c1 of
      Nothing -> Just c2
      Just ((n, e), cx) ->
        case n `IM.lookup` c2 of
          Nothing -> merge cx (IM.insert n e c2)
          Just e' ->
            if e == e'
              then merge cx c2
              else Nothing

spineLength :: Type v -> Int
spineLength (aType -> Just (ATArr a b)) =
  1 + spineLength b
spineLength _ = 0

dropArgs n t = aux n t []
  where
  aux 0 t l = (t, l)
  aux n (aType -> Just (ATArr a b)) l =
    aux (n-1) b (l++[a])
  aux _ _ _ = error "dropArgs"

matchSpine :: Eq v => Type v -> Type v -> Maybe [Type v]
matchSpine tgt u
  | lt > lu   = Nothing
  | u' == tgt = Just ea
  | otherwise = Nothing
  where
  (u', ea) = dropArgs (lu - lt) u
  lt = spineLength tgt
  lu = spineLength u

mkSpineType :: [Type v] -> Type v -> Type v
mkSpineType l t = aux l t
  where
  aux []     t = t
  aux (x:xs) t = x --> mkSpineType xs t

mkSpine :: [Term w w' v] -> Term w w' v -> Term w w' v
mkSpine l t = aux (reverse l) t
  where
  aux []     t = t
  aux (x:xs) t = App (aux xs t) x

monoType :: Type v -> TYPE v
monoType t = TYPE $ POLY 0 $ \[] -> fmap Free t

data SMaybe a = SNothing | SJust !a deriving(Eq, Ord, Show, Read)

fromSMaybe (SJust x) = Just x
fromSMaybe SNothing  = Nothing

instance Functor SMaybe where
  fmap _ SNothing  = SNothing
  fmap f (SJust x) = SJust (f x)

instance Applicative SMaybe where
  pure x = SJust x
  (SJust f) <*> (SJust x) = SJust $ f x
  _         <*> _         = SNothing

getMonoType' :: Type (FrBd v w) -> Maybe (Type v)
getMonoType' t = fromSMaybe $ traverse f t
  where
  f (Free x) = SJust x
  f _        = SNothing

getMonoType :: Type (FrBd v w) -> Maybe (Type v)
getMonoType t = traverse f t
  where
  f (Free x) = Just x
  f _        = Nothing

getMonoType'' :: TYPE v -> Maybe (Type v)
getMonoType'' (TYPE (POLY n p)) =
  getMonoType $ p $ replicate n ()

-- substitutions:
-- data VarSet w
-- data Subst w a
-- emptySub :: VarSet w -> Subst w a
-- addSub :: w -> a -> Subst w a -> Subst w a

-- First result list is type instantiation, second is arguments
-- This could introduce new type variables, but ATM we omit this case
--matchPolyNArgs :: Int -> Type v -> TYPE v -> Maybe ([Maybe (Type v)], [Either (Type v) (TYPE v)])
matchPolyNArgs :: (Eq v, Eq w) =>
  Int -> Type v -> Type (FrBd v w) ->
  Maybe ([(w, Type v)], [Either (Type v) (Type (FrBd v w))])
matchPolyNArgs n t ptype = {-# SCC "matchPolyNArgs" #-} force $ do
  l <- unify' (mkSpineType (map (TVar . Bound . Left) [0..n-1]) (fmap Free t)) (fmap (fmap Right) ptype)
  rb <- sequence $ mapMaybe realBound l
  return (rb, map snd $ sortBy (comparing fst) (mapMaybe args l))
  where
  realBound ((Right x), v) = {-# SCC "realBound" #-} Just $ do
    v' <- getMonoType v -- type should be deepSeq'ed perhaps
    return (x, v')
  realBound _              = {-# SCC "realBound" #-} Nothing
  args ((Left n), v) = {-# SCC "args" #-} Just (n, maybe (Right v') Left (getMonoType v'))
    where v' = fmap (fmap (either undefined id)) v
  args _             = {-# SCC "args" #-} Nothing
  force = {-# SCC "force" #-} withStrategy $
    seqTraverse $ -- Maybe
    seqPair
      (seqTraverse $ -- []
        seqPair r0 (seqTraverse r0))
      (seqTraverse $ -- []
        seqEither (seqTraverse r0) (seqTraverse r0))

seqEither :: Strategy a -> Strategy b -> Strategy (Either a b)
seqEither f g (Left a)  = Left  <$> f a
seqEither f g (Right b) = Right <$> g b

seqFrBd :: Strategy a -> Strategy b -> Strategy (FrBd a b)
seqFrBd f g (Free a)  = Free  <$> f a
seqFrBd f g (Bound b) = Bound <$> g b

matchPolyNArgsGuess :: (Eq v, Ord w, DiagnClass d, MonadPlus (d Gen)) =>
  Int -> [w] -> Gen (Type v) -> Type v -> Type (FrBd v w)
    -> (d Gen) ([(w, Type v)], [Type v], [Type v])
matchPolyNArgsGuess n vars guessType t ptype = {-# SCC "matchPolyNArgsGuess" #-} do
  -- MaybeT . return lifts Maybe a to MaybeT m a
  (tins, targs) <- {-# SCC "PNGrec" #-} case {-# SCC "PNGrec2" #-} matchPolyNArgs ({-# SCC "n" #-} n) ({-# SCC "t" #-} t) ({-# SCC "ptype" #-} ptype) of
    Nothing -> fail ""
    Just x -> return x
  case vars \\ map fst tins of
    [] -> fail "" --return (tins, map (either id undefined) targs, [])
    vd -> do
      extraTypes <- forM vd $ \x ->
        do
          e <- lift $ guessType
          return (x, e)
      let result = force
              ( tins ++ extraTypes
              , map (either id (join . fmap (frbd TVar $ \x -> fromJust $ lookup x extraTypes))) targs
              , map snd extraTypes)
      result `seq` return result
  where
  force = withStrategy $
    seqTriple
      (seqTraverse $ -- []
        seqPair r0 (seqTraverse r0))
      (seqTraverse $ -- []
        seqTraverse r0) 
      (seqTraverse $ -- []
        seqTraverse r0)

-- Tries to match b against the first argument of a and returns the result of a (possibly specialized)
matchPolyArg :: Eq v => TYPE v -> TYPE v -> Maybe (TYPE v)
matchPolyArg (TYPE (POLY n a)) (TYPE (POLY m b)) = do
  let a' = a $ map Left [0..n - 1]
  ATArr arg res <- aType a'
  l <- unify' arg (b $ map Right [0..m - 1])
  let aux (Bound x)  = maybe (TVar $ Bound x) id $ lookup x l
      aux y@(Free _) = TVar y
      res'           = res >>= aux
      polyArgs       = foldMap (frbd (const S.empty) S.singleton) res'
      s              = S.size polyArgs
      polyArgs'      = M.fromList $ zip (S.toList polyArgs) [0..]
  return $ TYPE $ POLY s $ \al -> fmap (fmap (\y -> al !! (fromJust $ M.lookup y polyArgs'))) res'

newtype MaybeT m a = MaybeT {runMaybeT :: m (Maybe a)}

instance (Functor m) => Functor (MaybeT m) where
  fmap f = MaybeT . fmap (fmap f) . runMaybeT

instance Monad m => Applicative (MaybeT m) where 
    pure = return
    (<*>) = ap
    
instance (Monad m) => Monad (MaybeT m) where
  fail _  = MaybeT (return Nothing)
  return  = lift . return
  x >>= f = MaybeT (runMaybeT x >>= maybe (return Nothing) (runMaybeT . f))

instance (Monad m, MonadPlus (MaybeT m)) => Alternative (MaybeT m) where
    (<|>) = mplus
    empty = mzero
    
instance (Monad m) => MonadPlus (MaybeT m) where
  mzero     = MaybeT (return Nothing)
  mplus x y = MaybeT $ do v <- runMaybeT x
                          case v of
                            Nothing -> runMaybeT y
                            Just _  -> return v

instance MonadTrans MaybeT where
  lift x = MaybeT (liftM Just x)

type MaybeGen = MaybeT Gen

data CallTree a =
  CLabel a (CallTree a) |
  CBranch (CallTree a) (CallTree a) |
  CFailed (CallTree a) (CallTree a) |
  CNil
  deriving (Eq, Show)

cBranch CNil x = x
cBranch x CNil = x
cBranch x y    = CBranch x y

cFailed CNil x = x
cFailed x y    = CFailed x y

pruneCTree (CLabel l@(n, _) a)
  | n > 1000  = CLabel l $ pruneCTree a
  | otherwise = CNil
pruneCTree (CBranch a b) = cBranch (pruneCTree a) (pruneCTree b)
pruneCTree (CFailed f b) = cFailed (pruneCTree f) (pruneCTree b)
pruneCTree CNil = CNil

pruneCTree' c = aux 10 c
  where
  aux 0 _             = CNil
  aux m (CLabel l a)  = CLabel l (aux (m - 1) a)
  aux m (CBranch a b) = cBranch (aux (m - 1) a) (aux (m - 1) b)
  aux m (CFailed f b) = cFailed (aux (m - 1) f) (aux (m - 1) b)
  aux _ CNil          = CNil

-- Diagnostics transformer
newtype DiagnT b m a = DiagnT {runDiagnT :: m (CallTree b, Maybe a)}

instance (Functor m) => Functor (DiagnT b m) where
  fmap f = DiagnT . fmap (\(c, x) -> (c, fmap f x)) . runDiagnT

instance Monad m => Applicative (DiagnT b m) where 
    pure = return
    (<*>) = ap

instance (Monad m) => Monad (DiagnT b m) where
  fail _  = DiagnT (return (CNil, Nothing))
  return  = lift . return
  x >>= f = DiagnT $ do
    (c, y)  <- runDiagnT x
    case y of
      Nothing -> return (c, Nothing)
      Just y' -> do
        (c', z) <- runDiagnT $ f y'
        return (cBranch c c', z)

instance (Monad m, MonadPlus (DiagnT b m)) => Alternative (DiagnT b m) where
    (<|>) = mplus
    empty = mzero

instance (Monad m) => MonadPlus (DiagnT b m) where
  mzero     = DiagnT (return (CNil, Nothing))
  mplus x y = DiagnT $ do p@(c, v) <- runDiagnT x
                          case v of
                            Nothing -> do
                              (c', v') <- runDiagnT y
                              return (cFailed c c', v')
                            Just _  -> return p

instance MonadTrans (DiagnT b) where
  lift x = DiagnT (liftM (\z -> (CNil, Just z)) x)

class MonadTrans d => DiagnClass d where
  cLabel :: Monad m => String -> d m a -> d m a

--cLabel :: Monad m => b -> DiagnT b m a -> DiagnT b m a
{-
instance DiagnClass DiagnT where
  cLabel x g = DiagnT $ do
    (c, y) <- runDiagnT g
    return (CLabel x c, y)
-}

instance DiagnClass (DiagnT (Integer, String)) where
  --cLabel'' :: Monad m => b -> DiagnT (Integer, b) m a -> DiagnT (Integer, b) m a
  cLabel x g = DiagnT $ do
    --t1 <- cpuTimeM
    let t1 = cpuTime ()
    (c, y) <- t1 `seq` runDiagnT g
    --t2 <- cpuTimeM
    let t2 = cpuTime ()
    t2 `seq` return (CLabel ((t2 - t1) `div` 1000000000, x) c, y)

instance DiagnClass MaybeT where
  --cLabel' :: Monad m => b -> MaybeT m a -> MaybeT m a
  cLabel _ = id

type DiagnGen b = DiagnT b Gen

--type MyGen = DiagnGen (Integer, String)
type MyGen = MaybeGen

permute :: [a] -> Gen [a]
permute xs = do
  v <- vector l :: Gen [Int]
  let p = map snd $ sortBy (comparing fst) $ zip v [0..]
  return $ debug $ map (xs!!) p
  where
  l = length xs
  debug x = x -- if l >= 50 then ("\npermute: " ++ show l ++ "\n") `trace` x else x

permute' :: [a] -> Gen [a]
permute' xs = do
  v <- vector l :: Gen [Int]
  let p = map snd $ sortBy (comparing fst) $ zip v [0..]
  return $ map (xs!!) p
  where
  l = length xs

-- Weights must be positive!
permuteWeighted :: [(Int, a)] -> Gen [a]
permuteWeighted xs = do
  v <- mapM (\n -> replicateM n arbitrary >>= \ns -> return $ minimum ns) (map fst xs) :: Gen [Int]
  --v <- vector l :: Gen [Int]
  let p = map snd $ sortBy (comparing fst) $ zip v [0..]
  return  $ map ((map snd xs)!!) p
  where
  l = length xs

--randomOrder :: [MaybeGen a] -> MaybeGen a
randomOrder :: (DiagnClass d, MonadPlus (d Gen)) => [(d Gen) a] -> (d Gen) a
randomOrder xs = do
  v <- lift $ permute xs
  msum v

randomOrderWeighted :: (DiagnClass d, MonadPlus (d Gen)) => [(Int, (d Gen) a)] -> (d Gen) a
randomOrderWeighted xs = do
  v <- lift $ permuteWeighted xs
  msum v

data OpenTerm v = OpenTerm (forall w w'. ([w], [w']) -> Term v w' (FrBd (w, [Type v]) w'))
--data OpenTerm v = OpenTerm (forall w w' w''. ([w], [w']) -> Term v w'' (FrBd (FrBd (w, [Type v]) w') w''))

openId n = OpenTerm (\e -> Lam (TVar undefined) $ \x -> aux n x)
  where
  aux 0 x = Var (Bound x)
  aux n x = Lam (TVar undefined) $ \_ -> aux (n - 1) x

l !!! n
  | length l > n = l !! n
  | otherwise    = error $ "!!!: index too large: " ++ show n ++ ", length: " ++ show (length l)

{-# NOINLINE cpuTime #-}
cpuTime () = unsafePerformIO getCPUTime

cpuTimeM :: Monad m => m Integer
cpuTimeM = do
  let t = cpuTime ()
  t `seq` return t

takeTime n = foldl' (+) 0 $ replicate n 0

takeTimeM n = do
  let x = takeTime n
  x `seq` return ()

arbExpAux :: forall v d. (Show v, Ord v, DiagnClass d, MonadPlus (d Gen)) =>
  Bool -> Int -> Int -> [(TYPE v, [Int])] -> Int -> [TYPE v] -> [Type v] -> Type v ->
--arbExpAux :: (Show v, Ord v) => Int -> Int -> [(TYPE v, [Int])] -> [(Type v, [Int])] -> Int -> Type v ->
  (d Gen) (OpenTerm v)
arbExpAux useSeq n ng p lp cl m t
  | typeSize t > n + 15 = mzero
  | otherwise = {-# SCC "arbExpAux" #-}
  cLabel ("target: " ++ unparseType t ++ ", n: " ++ show n) $
  randomOrderWeighted $
    -- direct match with monomorphic var
    ({-# SCC "direct_mono" #-}
    [ (4, cLabel "direct mono" $
      lift $ liftM (\nn -> OpenTerm $ \(_, v) ->
              Var (Bound $ v!!nn)) (frequency $ zip (reverse [l..2 * l]) (map return xs)))
      | let xs = [ x | (t', x) <- zip m [0..] , t' == t ]
            l  = length xs
      , not (null xs)
    ]) ++ -- direct match with polymorphic var
    ({-# SCC "direct_poly" #-} -- use random order here
    [ (2, cLabel "direct poly" $
      lift $ do
        (x, sub, t') <- elements xs
        nn <- elements x
        return $ OpenTerm $ \(pv, _) ->
                  Var (Free (pv!!nn, map fromJust sub)))
      | let xs = [ (x, sub, t') | (t', x) <- p, Just sub <- [exactMatch t' t] ]
            l  = length xs
      , not (null xs)

    --[ randomOrder [ do
    --    case exactMatch t' t of
    --      Nothing -> mzero
    --      Just sub -> return $ OpenTerm $ \(pv, _) ->
    --              Var (pv!!x) (Just (map fromJust sub))
    --  | (t', x) <- zip p [0..]]
    ]) ++ -- match with monomorphic var with extra args
    ({-# SCC "extra_mono" #-}
    [ (4, cLabel "extra mono" $
      do
        (nn, tl) <- lift $ frequency $ zip (reverse [l..2 * l]) (map return xs)
        let l = length tl
        args <- mapM (arbExpAux useSeq ((n - l - 1) `div` l) ng p lp cl m) tl
        return $ OpenTerm $ \e@(_, v) ->
          mkSpine (map (\(OpenTerm a) -> a e) args) (Var (Bound $ v!!nn)))
      | let xs = [ (x, tl) | (t', x) <- zip m [0..] , Just tl <- [matchSpine t t'] ]
            l  = length xs
      , not (null xs)
      , n > 2
    ]) ++ -- match with polymorphic var with extra args
    ({-# SCC "extra_poly" #-}
    {-[ do
        (nn, tins, targs) <- lift $ (frequency $ zip (reverse [l..2 * l]) (map return xs))
        let l = length targs
        args <- mapM (arbExpAux ((n - 1) `div` l) p m) targs
        return $ OpenTerm $ \e@(pv, _) -> mkSpine (map (\(OpenTerm a) -> a e) args) $ Var (pv!!nn) (Just tins)
      | n > 3
      , let xs = [ (x, map snd $ sortBy (comparing fst) tins, map (either id undefined) targs)
                 | (TYPE (POLY nn tf), x) <- zip p [0..]
                 ,  let t' = tf [0..nn-1]
                 ,  np <- [0..3]
                 ,  Just (tins, targs) <- [matchPolyNArgs np t t']
                 ,  length tins == nn ]
            l  = length xs
      , not (null xs)-}
    [ (2, cLabel "extra poly" $
      randomOrder [ cLabel ("tt: " ++ unparseTYPE tt ++ ", np: " ++ show np) $ do
        case matchPolyNArgs np t t' of
          Nothing -> mzero
          Just (tins, targs) -> do
            let tins'  = {-# SCC "tins'" #-} map snd $ sortBy (comparing fst) tins
                targs' = {-# SCC "targs'" #-} map (either id undefined) targs
                l = length targs'
            if not (length tins == nn) then mzero else cLabel ("extra poly success: " ++ unparseType (tApply' tt tins')) $ do
              args <- {-# SCC "mapM" #-} mapM (arbExpAux useSeq ((n - l - 3) `div` l) ng p lp cl m) targs'
              xx <- lift $ elements x
              return $ {-# SCC "OpenTerm" #-} OpenTerm $ \e@(pv, _) ->
                {-# SCC "mkSpine" #-} mkSpine (map (\(OpenTerm a) -> a e) args) $ Var (Free (pv!!xx, tins'))
        |  (tt@(TYPE (POLY nn tf)), x) <- p
        ,  let t' = tf [0..nn-1]
        ,  np <- if n > 6 then [1..3] else [1]
      ]) | n > 3
    ]) ++ -- match with polymorphic var with extra args and guessed types
    ({-# SCC "extra_poly_guess" #-}
    [ (2, cLabel "extra poly guess" $
      do
        --(tins, targs, extra) <- matchPolyNArgsGuess np [0..nl-1] (randomType' l1 ct) t t'
        (tins, targs, extra) <- matchPolyNArgsGuess np [0..nl-1] (randomType' l1 cl) t t'
        cLabel ("extra types: " ++ show extra) $ do
          let tins' = map snd $ sortBy (comparing fst) tins
          --("t': " ++ show t' ++ ", np: " ++ show np ++ ", targs length: " ++ show (length targs)) `trace` return ()
          --("tins': " ++ show (length tins')) `trace` return ()
          args <- mapM (arbExpAux useSeq ((n - np - 4) `div` np) (ng - 1) p lp cl m) targs
          --("args successful: " ++
          --  show [f (['a'..], ['A'..]) | OpenTerm f <- args]) `trace` return ()
          nn <- lift $ elements x
          return $ OpenTerm $ \e@(pv, _) ->
            mkSpine (map (\(OpenTerm a) -> a e) args) $ Var (Free (pv!!nn, tins')))
      | n > 10
        , ng > 0
        , (TYPE (POLY nl tf), x) <- p
        , let t' = tf [0..nl-1]
        --, let ct = {-# SCC "ct1" #-} closeTypes' 3 (map monoType m ++ map fst p)
        , np <- [1..3]
        , let l1 = (n - 10) `div` 2
        , not $ null $ map monoType m ++ map fst p
    ]) ++ -- Lambda
    ({-# SCC "lambda" #-}
    [ (8, cLabel "lambda" $
      liftM (\(OpenTerm b) ->
        OpenTerm $
          \(pv, mv) ->
            Lam ta (\nv -> b (pv, nv:mv))) (arbExpAux useSeq (n-1) ng p lp (addToClosure cl ta) (ta:m) tb))
      | Just (ATArr ta tb) <- [aType t], n > 1
    ]) ++ -- App
    ({-# SCC "app" #-} -- TODO instead of trying hard here, just eta-expand
    [ (8, cLabel "app" $
      do
        --tbs <- replicateM 5 $ lift $ randomType' l1 ct
        tbs <- replicateM 5 $ lift $ randomType' l1 $ cl
        msum [ do
          let n2 = (n - 1) `div` 2
          OpenTerm a <- arbExpAux useSeq n2 (ng - 1) p lp cl m (tb --> t)
          let remainder = do
                OpenTerm b <- arbExpAux useSeq n2 (ng - 1) p lp cl m tb
                return $ OpenTerm $ \e -> App (a e) (b e)
          --case a (replicate lp False, replicate lm False) of
          -- This is quite brain-dead - this is because I should convert
          -- all free variables into 'Free x' instead of keeping them
          -- as 'Bound y'
          let a' :: Term v Bool (FrBd ((), [Type v]) Bool)
              a' = a (replicate lp (), replicate lm False)
          case a' of
            Lam _ f ->
              --if or $ freeVars $ boundToFree (case a'' of Lam _ f -> f) True
              if or $ freeVars' False $ mapTerm (const False) (frbd (Free . fst) Bound) $ f True
                then remainder
                else mzero
            _ -> remainder
          | tb <- tbs ])
    | n > 7
    , ng > 0
    --, let ct = {-# SCC "ct2" #-} closeTypes' 3 (map monoType m ++ map fst p)
    , let l1 = (n - 7) `div` 2
    , not $ null $ map monoType m ++ map fst p
    ]) ++ -- Seq
    ({-# SCC "seq" #-}
    [ (6, cLabel "seq" $ do
      (v, vn) <- lift $ elements $ zip m [0..]
      liftM (\(OpenTerm b) ->
        OpenTerm $ \e@(pv, mv) ->
          App (App (Var (Free (pv!!0, [v, t]))) (Var (Bound (mv!!vn)))) (b e)) (arbExpAux useSeq (n-2) ng p lp cl m t))
      | useSeq, not $ null m, n > 1])
  where
  lm = length m
  --lp = length p
  --l !-! x = l !! (nm - 1 - x)

arbExp :: (Show v, Ord v, DiagnClass d, MonadPlus (d Gen)) =>
  Bool -> Int -> Int -> [TYPE v] -> Type v -> (d Gen) (CTerm v)
arbExp useSeq n ng p t = do
  let p' = map (\x -> (fst $ head x, map snd x)) $
            groupBy (\x y -> fst x == fst y) $
            sortBy (comparing fst) $
            (if useSeq then (filter ((/= 0) . snd)) else id) $ -- remove seq from the environment
              zip p [0..]
      ct = closeTypes' 3 $ map fst p'
  _ <- return ()
  (OpenTerm x) <-
    arbExpAux useSeq n ng p'
      (if useSeq then (- 1) else id (length p)) ct [] t
  return (CTerm p (\v -> x (v, [])))

arbExpPrint :: forall v. (Ord v, Show v) => Bool -> Int -> Int -> [TYPE v] -> Type v -> IO ()
arbExpPrint useSeq n ng p t = do
  let env = ['A'..]
  putStrLn $ "Environment: " ++ (concat $ intersperse ", " $ zipWith (\pt pv -> [pv] ++ ":" ++ show pt) p env)
  --exprs <- sample' $ runDiagnT (arbExp n ng p t)
  exprs <- sample' $ runMaybeT (arbExp useSeq n ng p t)
  --let exprs' = map (\(c, x) -> (pruneCTree c, fmap (\(CTerm _ e) -> e env) x)) exprs
  let exprs' :: [Maybe (Term v Char (FrBd (Char, [Type v]) Char))]
      exprs' = map (\x -> fmap (\(CTerm _ e) -> e env) x) exprs
  mapM_ print exprs'
  --print $ all (maybe True (isJust . termWF) . snd) exprs
  print $ all (maybe True (isJust . termWF)) exprs

cartN 0 _ = pure []
cartN n l = (:) <$> l <*> cartN (n - 1) l

fastNub :: Ord a => [a] -> [a]
fastNub = map head . group . sort

closeTypes :: (Ord v) => Int -> [Type v] -> [TYPE v] -> [Type v]
closeTypes n m p = fst $ aux n (fastNub m, fastNub p)
  where
  aux 0 x = x
  aux n (m, p) = aux (n - 1)
    (
    do
      x <- m
      y <- m
      maybeToList $ tryApply x y
    `mplus`
    do
      pt <- p
      tryApplyP m pt,
    p)
  tryApply (aType -> Just (ATArr a b)) ac
    | a == ac   = Just b
    | otherwise = Nothing
  tryApply _ _ = Nothing
  -- here arguments are in reverse
  tryApplyP :: [Type v] -> TYPE v -> [Type v]
  tryApplyP allTypes pt@(TYPE (POLY n _)) =
    tApply' pt <$> cartN n allTypes

-- TODO: filter out monotypes and make a new generator

-- Tries to make new poly types by applying existing types to eachother
-- We should also prune specialized types and leave more general ones (within reason)
closeTypes' :: (Ord v) => Int -> [TYPE v] -> [TYPE v]
closeTypes' n p = (\(x, y) -> S.toList x ++ S.toList y) $ myIter n (S.fromList p)
  where
  sizeLimit = 18
  myIter n initial =
    iterate myIterAux (S.empty, initial) !! n
  -- In every iteration we try applying types to eachother, except that
  -- we don't try it with old types against old types (these have been tried)
  myIterAux (old, new) =
    (newOlds, S.fromList newCandidates S.\\ newOlds)
    where
    new' = S.toList new
    old' = S.toList old
    newCandidates =
      do
        x <- new'
        y <- old' ++ new' -- new-old, new-new
        z <- maybeToList $ matchPolyArg x y
        guard $ tYPESize z < sizeLimit
        return z
      `mplus`
      do
        x <- old'
        y <- new' -- old-new
        z <- maybeToList $ matchPolyArg x y
        guard $ tYPESize z < sizeLimit
        return z
    newOlds = old `S.union` new

addToClosure :: Ord v => [TYPE v] -> Type v -> [TYPE v]
addToClosure sl mt = if S.member t s then sl else S.toList (t `S.insert` (s `S.union` S.fromList new))
  where
  sizeLimit = 18
  t = monoType mt
  s = S.fromList sl
  new = do
    x <- sl
    z <- maybeToList $ matchPolyArg x t
    guard $ tYPESize z < sizeLimit
    return z
    `mplus`
    do
    x <- sl
    z <- maybeToList $ matchPolyArg t x
    guard $ tYPESize z < sizeLimit
    return z

randomType :: Int -> [Type v] -> Gen (Type v)
randomType s base =
  frequency $
    [ (1, elements base) ] ++
    [ (1, liftM2 (-->) (randomType (s`div`2) base) (randomType (s`div`2) base)) | s > 0]

randomType' :: Int -> [TYPE v] -> Gen (Type v)
randomType' n l = forceGenType $ aux n
  where
  aux n =
    frequency $
      [ (4, oneof $ map (base n) l' ) | let l' = filter (\x -> tYPESize x < 3) l, not $ null l' ] ++
      [ (4, oneof $ map (base n) l' ) | let l' = filter (\x -> tYPESize x < n + 2) l, not $ null l' ] ++
      [ (2, oneof $ map (base n) l' ) | let l' = filter (\x -> tYPESize x < n * 2 + 8) l, not $ null l' ] ++
      [ (1, liftM2 (-->) (aux (n `div` 2)) (aux (n `div` 2))) | n > 3]
  monoTypes = catMaybes $ map getMonoType'' l
  base m p@(TYPE (POLY n _)) = do
    v <- vectorOf n $ elements (filter (\x -> typeSize x < m * 2 + 4) monoTypes)
    return $ tApply' p v

-- Doesn't seem to make a big difference
forceGenType = id -- fmap (withStrategy $ seqTraverse r0)

unparse l (CTerm penv f) = aux ['a'..] t
  where
  addTypes (v, True)  t = (v, Just t)
  addTypes (v, False) _ = (v, Nothing)
  t = f (zipWith addTypes l penv)
  aux :: Show v => [Char] -> Term v [Char] (FrBd (([Char], Maybe (TYPE v)), [Type v]) [Char]) -> [Char]
  aux _      (Var (Free ((x, Nothing) , _)))  = x
  aux _      (Var (Free ((x, Just t), tins))) = "(" ++ x ++ "::" ++ unparseType (tApply' t tins) ++ ")"
  aux _      (Var (Bound y)) = y
  aux (v:vs) (Lam _ t)   = "\\" ++ [v] ++ " -> " ++ aux vs (t [v])
  aux vs     (App t1 t2) = b1 (aux' vs t1) ++  " " ++ b2 (aux vs t2)
    where
    b1 = case t1 of
      Lam _ _ -> bracket
      _       -> id
    b2 = case t2 of
      App _ _ -> bracket
      Lam _ _ -> bracket
      _       -> id
    aux' vs (App t1 t2) = b1 (aux' vs t1) ++  " " ++ b2 (aux vs t2)
      where
      b1 = case t1 of
        Lam _ _ -> bracket
        _       -> id
      b2 = case t2 of
        App _ _ -> bracket
        Lam _ _ -> bracket
        _       -> id
    aux' vs x = aux vs x

unparse' l (CTerm penv f) = aux ['a'..] t
  where
  addTypes (v, True)  t = (v, Just t)
  addTypes (v, False) _ = (v, Nothing)
  t = f (zipWith addTypes l penv)
  aux :: Show v => [Char] -> Term v [Char] (FrBd (([Char], Maybe (TYPE v)), [Type v]) [Char]) -> [Char]
  aux _      (Var (Free ((x, Nothing) , _)))  = x
  aux _      (Var (Free ((x, Just t), tins))) = "(" ++ x ++ "::" ++ unparseType (tApply' t tins) ++ ") (sizes: " ++
    show (map typeSize tins) ++ ")"
  aux _      (Var (Bound y)) = y
  aux (v:vs) (Lam tt t)  = "\\" ++ [v] ++ ":" ++ unparseType tt ++ " -> " ++ aux vs (t [v])
  aux vs     (App t1 t2) = b1 (aux' vs t1) ++  " " ++ b2 (aux vs t2)
    where
    b1 = case t1 of
      Lam _ _ -> bracket
      _       -> id
    b2 = case t2 of
      App _ _ -> bracket
      Lam _ _ -> bracket
      _       -> id
    aux' vs (App t1 t2) = b1 (aux' vs t1) ++  " " ++ b2 (aux vs t2)
      where
      b1 = case t1 of
        Lam _ _ -> bracket
        _       -> id
      b2 = case t2 of
        App _ _ -> bracket
        Lam _ _ -> bracket
        _       -> id
    aux' vs x = aux vs x

toModule t =
  "module Main where\n" ++
  "import Control.Monad\n" ++
  "import qualified Control.Exception as E\n" ++
  "import System.IO (hSetBuffering, stdout, BufferMode (NoBuffering))\n" ++
-- need 2 versions perhaps?
  --"handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \" ++ s\n" ++
  "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \"\n" ++
  "incomplete1 0 = [undefined]\n" ++
  "incomplete1 n = n:(incomplete1 (n-1))\n" ++
  "incomplete2 0 = undefined\n" ++
  "incomplete2 n = n:(incomplete2 (n-1))\n" ++
  "enumFromTo' a n = enumFromTo a (a + n)\n" ++
  "case1 c' e' l' = case l' of x':xs' -> c' x' xs'; [] -> e'\n" ++
  "code = (" ++ t ++ ")\n" ++
  "main = do\n" ++
  "  hSetBuffering stdout NoBuffering\n" ++
  "  forM_ [0..5] $ \\x -> do\n" ++
  "    E.catch (print $ code $ incomplete1 x) handler\n" ++
  "  forM_ [0..5] $ \\x -> do\n" ++
  "    E.catch (print $ code $ incomplete2 x) handler\n"

toModuleMany sep tl =
  "module Main where\n" ++
  "import Control.Monad\n" ++
  "import qualified Control.Exception as E\n" ++
  "import System.IO (hSetBuffering, stdout, BufferMode (NoBuffering))\n" ++
-- need 2 versions perhaps?
  --"handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \" ++ s\n" ++
  "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \"\n" ++
  "incomplete1 0 = [undefined]\n" ++
  "incomplete1 n = n:(incomplete1 (n-1))\n" ++
  "incomplete2 0 = undefined\n" ++
  "incomplete2 n = n:(incomplete2 (n-1))\n" ++
  "incomplete3 n 0 = undefined:reverse [0..n-1]\n" ++
  "incomplete3 n m = n:incomplete3 (n-1) (m-1)\n" ++
  "enumFromTo' a n = enumFromTo a (a + n)\n" ++
  "case1 c' e' l' = case l' of x':xs' -> c' x' xs'; [] -> e'\n" ++
  "codeList = " ++ tl ++ "\n" ++
  "main = do\n" ++
  "  hSetBuffering stdout NoBuffering\n" ++
  "  forM_ codeList $ \\code -> do\n" ++
  "    forM_ [0..5] $ \\x -> do\n" ++
  "      E.catch (print $ code $ incomplete1 x) handler\n" ++
  "    forM_ [0..5] $ \\x -> do\n" ++
  "      E.catch (print $ code $ incomplete2 x) handler\n" ++
  "    forM_ [0..5] $ \\x -> forM_ [0..x] $ \\y -> do\n" ++
  "      E.catch (print $ code $ incomplete3 x y) handler\n" ++
  "    putStrLn \"" ++ sep ++"\"\n"

isFailure (ExitFailure _) = True
isFailure _               = False

mAssert True = return ()
mAssert False = fail "mAssert"

printTestCase' :: Testable prop => String -> prop -> Property
printTestCase' s =
  callback $ PostTest NotCounterexample $ \st res ->
    if Prop.ok res == Just False
      then putLine (terminal st) s
      else return ()

printSeed p =
  callback (PostTest NotCounterexample $ \s r ->
    if Prop.ok r == Just False
      then putStrLn $ "failed: seed: " ++ show (randomSeed s) ++
            " size: " ++ show (computeSize s (numSuccessTests s) (numDiscardedTests s))
      else return ()) p

compareOutputs o1 o2 =
  and $ zipWith cmpLine l1 l2
  where
  l1 = lines o1
  l2 = lines o2
  cmpLine x y
    | take 15 x == "*** Exception: " &&
      take 15 y == "*** Exception: "    = True
    | otherwise                         = x == y

compareMany sep o1 o2 =
  length $ filter id $
    zipWith (/=)
            (splitOutputs $ lines o1)
            (splitOutputs $ lines o2)
  where
  splitOutputs x = let (p, l) = foldr f ([], []) x
                 in p : l
  f l (p, rest)
    | l == sep  = ([], p:rest)
    | otherwise = (l:p, rest)

runWait c = do
  p <- runCommand c
  waitForProcess p

generatePrint useSeq n ng env l t =
  forAllShrink (runMaybeT $ arbExp useSeq n ng env' (fmap Name t)) (shrinkCTerm' []) $ \x ->
  monadicIO $ do
    pre $ isJust x
    let Just x' = x
    run $ putStrLn ""
    run $ putStrLn $ unparse l x'
    run $ putStrLn $ unparse' l x'
    assert $ isJust $ termWF x'
    run $ putStrLn "Well formed!"
  where
  env' = map (fmap Name) env

generatePrint' useSeq n ng env t =
  generatePrint useSeq n ng (map snd env) (map fst env) t

testGHC n ng env l =
  printSeed $
  let t = listType (TVar "Int") --> listType (TVar "Int") in
  --let t = listType (listType (TVar "Int") --> listType (TVar "Int")) in
  let env' = map (fmap Name) env in
  forAllShrink (runMaybeT $ arbExp True n ng env' (fmap Name t)) (shrinkCTerm' []) $ \x ->
  --forAllShrink (runDiagnT $ arbExp True n ng env' (fmap Name t)) shrinkCTerm'' $ \(c, x) ->
  monadicIO $ do
    pre $ isJust x
    let Just x' = x
        --c' = pruneCTree (c :: CallTree (Integer, String))
    --pre $ c' /= CNil
    --if c' /= CNil
    --  then do
    --pre $ (any (== "tail") $ words $ unparse l x') && (unparse l x' /= "tail")
    do
        run $ putStrLn ""
        run $ putStrLn $ unparse l x'
        run $ putStrLn $ unparse' l x'
        --run $ putStrLn $ show x'
--        run $ mapM_ (putStrLn . unparse l) $ shrinkCTerm x'
        --run $ putStrLn $ show $ pruneCTree' c'
        run $ putStrLn ""
    --  else return ()
    assert $ isJust $ termWF x'
    run $ putStrLn "Well formed!"
    r <- run $ runMaybeT $ do
      (assertion, outPlain, outOpt) <- testTerm $ toModule $ unparse l x'
      let finalAssertion = assertion && (outPlain == outOpt)
      when (not finalAssertion) $ lift $ do
        putStrLn $ "failed on this one: " ++ unparse l x'
        p <- runCommand "cp TestModule.hs TestModule.hs~failed"
        waitForProcess p
        return ()
      mAssert $ finalAssertion
    --run $ putStrLn ""
    assert $ isJust r
    
testTerm t = do
  {-when (c' /= CNil) $ -}
  lift $ withFile "TestModule.hs" WriteMode $ \h -> do
    hPutStrLn h t
  lift $ runWait "rm TestModule.o"
  e1 <- lift $ runWait "ghc -o testModule TestModule.hs"
  mAssert $ not $ isFailure e1
  lift $ runWait "rm TestModule.o"
  e2 <- lift $ runWait "ghc -o testModuleOpt TestModule.hs -O2"
  mAssert $ not $ isFailure e2
  (e3, out3, _) <- lift $ readProcessWithExitCode "./testModule" [] ""
  (e4, out4, _) <- lift $ readProcessWithExitCode "./testModuleOpt" [] ""
  --lift $ putStr out3
  --monitor (whenFail $ putStrLn $ "normal:\n" ++ out3 ++ "opt:\n" ++ out4)
  let assertion = isFailure e3 == isFailure e4
  return (assertion, out3, out4)

-- forAllShrink with custom printing
forAllShrinkPrt gen shrinker prt pf =
  MkProperty $ 
  gen >>= \x ->
    unProperty $
    shrinking shrinker x $ \x' ->
      printTestCase (prt x') (pf x')

printMCTerms l cc = showListWith (\x s -> unparse l x ++ s) cc' $
  case rest of
    [] -> ""
    _  -> " and " ++ show (length rest) ++ " more"
  where
  cutoff      = 10
  (cc', rest) = splitAt cutoff $ catMaybes cc

testGHCMany listL n ng env l =
  --printSeed $
  let t = listType (TVar "Int") --> listType (TVar "Int") in
  --let t = listType (listType (TVar "Int") --> listType (TVar "Int")) in
  let env' = map (fmap Name) env in
  --forAll (return ()) $ \() ->
  forAllShrinkPrt
    (vectorOf (listL + 5) (runMaybeT $ arbExp True n ng env' (fmap Name t)))
    (shrinkList $ shrinkCTerm' [0]) (printMCTerms l) $ \xl ->
    --(shrinkList shrinkNothing) $ \xl ->
  --forAllShrink (runDiagnT $ arbExp True n ng env' (fmap Name t)) shrinkCTerm'' $ \(c, x) ->
  monadicIO $ do
    let xl' = take listL $ catMaybes xl
    let sep = "===="
    --pre $ length xl' == listL
    pre $ not $ null xl'
        --c' = pruneCTree (c :: CallTree (Integer, String))
    --pre $ c' /= CNil
    do
          --run $ putStrLn ""
          --run $ putStrLn $ unparse l x'
          --run $ putStrLn $ unparse' l x'
      assert $ all isJust $ map termWF xl'
      --run $ putStrLn "Well formed!"
      --when (length xl' == 1) $ monitor $ printTestCase' $ unparse' l (xl'!!0)
      --when (length xl' == 1) $ monitor $ printTestCase' $ unparse l (xl'!!0)
      r <- run $ runMaybeT $ do
        (assertion, outPlain, outOpt)
          <- testTerm
            $ toModuleMany sep
            $ showListWith (\t s -> "\n  " ++ unparse l t ++ s) xl' ""
        let numDifferent   = compareMany sep outPlain outOpt
            finalAssertion = assertion && (numDifferent == 0)
        when (not finalAssertion) $ lift $ do
          --putStrLn $ "failed on this one: " ++ unparse l x'
          p <- runCommand "cp TestModule.hs TestModule.hs~failed"
          waitForProcess p
          return ()
        return (finalAssertion, numDifferent)
      --monitor $ printTestCase' $ "terms sizes = " ++ show (map cTermSize xl')
      case r of
        Just (a, nd) -> 
          assert a
          --monitor $ collect nd
          --monitor $ collect (length xl')
        Nothing -> assert False -- compilation error?

undefinedType = TYPE (POLY 1 $ \[a] -> TVar (Bound a))

tBool = TVar $ Free "Bool"
mTBool = monoType (TVar "Bool")

secTypes =
  [ (("True",   False), mTBool)
  , (("False",  False), mTBool)
  , (("(&&)",   False), monoType $ TVar "Bool" --> TVar "Bool" --> TVar "Bool")
  , (("(||)",   False), monoType $ TVar "Bool" --> TVar "Bool" --> TVar "Bool")
  , (("iftl",   False), TYPE (POLY 1 $ \[a] -> tBool --> TVar (Bound a) --> TVar (Bound a) --> TVar (Bound a)))
  , (("return", False), TYPE (POLY 1 $ \[a] -> TVar (Bound a) --> monadType (TVar (Bound a))))
  , (("(>>=)",  False), TYPE (POLY 2 $ \[a, b] ->
        monadType (TVar (Bound a)) --> (TVar (Bound a) --> monadType (TVar (Bound b))) --> monadType (TVar (Bound b))))
  , (("(>>=)",  False), TYPE (POLY 2 $ \[a, b] ->
        monadType (TVar (Bound a)) --> (TVar (Bound a) --> monadType (TVar (Bound b))) --> monadType (TVar (Bound b))))
  , (("(>>=)",  False), TYPE (POLY 2 $ \[a, b] ->
        monadType (TVar (Bound a)) --> (TVar (Bound a) --> monadType (TVar (Bound b))) --> monadType (TVar (Bound b))))
  , (("(>>=)",  False), TYPE (POLY 2 $ \[a, b] ->
        monadType (TVar (Bound a)) --> (TVar (Bound a) --> monadType (TVar (Bound b))) --> monadType (TVar (Bound b))))
  ]
testGHC' n ng env = testGHC n ng (map snd env) (map fst env)
testGHCMany' listL n ng env = testGHCMany listL n ng (map snd env) (map fst env)

-- it's possible to fake a bound var
-- should change ALL free vars?
freeMap f term = aux term
  where
  aux (Lam t g)       = Lam t (\(Bound v) -> aux $ g (Bound v))
  aux (App t1 t2)     = App (aux t1) (aux t2)
  aux (Var (Free x))  = Var (Free $ f x)
  aux (Var (Bound y)) = Var (Bound y)

freeMap' f term = aux term
  where
  aux (Lam t g)       = Lam t (\(Bound v) -> aux $ g (Bound v))
  aux (App t1 t2)     = App (aux t1) (aux t2)
  aux (Var (Free x))  = Var (f x)
  aux (Var (Bound y)) = Var (Bound y)

shrinkCTerm' _ (Nothing) = []
shrinkCTerm' f (Just t)  = map (\x -> (Just x)) $ shrinkCTerm2 f t

shrinkCTerm'' (_, Nothing) = []
shrinkCTerm'' (c, Just t)  = map (\x -> (CNil, Just x)) $ shrinkCTerm2 [] t

shrinkAux :: forall v w w'. Eq v =>
  [Int] ->
  [(TYPE v, w)] ->
  (forall w1. Term v w1 (FrBd (Type v, (w, [Type v])) w1)) ->
  [Term v w' (FrBd (w, [Type v]) w')]
shrinkAux forbid env t = map ($ []) $
  replaceWithSubTerms 0 (mapTerm id (frbd (Just . Free) (fmap Bound)) t)
  `mplus`
  replaceFromEnv 0 t
  `mplus`
  betaReduce 0 (mapTerm id (frbd (Free . Free) Bound) t)
  where
  noShrink :: Int ->
    Term v (Type v, Int) (FrBd (Type v, (w, [Type v])) (Type v, Int)) ->
    [w'] -> Term v w' (FrBd (w, [Type v]) w')
  -- again free vars should be really converted into free
  --noShrink :: Int ->
  --  (forall b. Term v b (FrBd (TYPE v, w) b)) ->
  --  [w'] -> Term v w' (FrBd w w')
  noShrink n t = case t of
    Var (Free (_, x))  -> \l -> Var (Free x)
    Var (Bound (_, m)) -> \l -> Var (Bound $ l !! (n - 1 - m))
    Lam tt f           -> \l ->
      Lam tt $ \x -> noShrink (n + 1) (f (tt, n)) (x:l)
    App t1 t2          -> \l ->
      App (noShrink n t1 l) (noShrink n t2 l)

  replaceFromEnv :: Int ->
    Term v (Type v, Int) (FrBd (Type v, (w, [Type v])) (Type v, Int)) ->
    [[w'] -> Term v w' (FrBd (w, [Type v]) w')]
  replaceFromEnv n t =
    case t of
      Var (Free _)  -> mzero
      Var (Bound _) -> fromEnv
      Lam tt f      ->
        fromEnv
        `mplus`
        do
          t' <- replaceFromEnv (n + 1) (f (tt, n))
          return $ \l -> Lam tt $ \x -> t' (x:l)
      App t1 t2     ->
        fromEnv
        `mplus`
        do
          t1' <- replaceFromEnv n t1
          return $ \l -> App (t1' l) (noShrink n t2 l)
        `mplus`
        do
          t2' <- replaceFromEnv n t2
          return $ \l -> App (noShrink n t1 l) (t2' l)
    where
    Just ttype = termWF's $ mapTerm (\x -> (x, 0)) (frbd fst fst) t
    env' = map fst $ filter snd $ zip env (map (`elem` forbid) [0..])
    fromEnv = do
      (p, v) <- env
      tm <- maybeToList $ exactMatch p ttype
      return $ \l -> Var (Free (v, (map fromJust tm)))

  subTerms :: Int -> Type v ->
    Term v (Maybe (Type v, Int)) (Maybe (FrBd (Type v, (w, [Type v])) (Type v, Int))) ->
    [[w'] -> Term v w' (FrBd (w, [Type v]) w')]
  subTerms n target t =
    do
      ttype <- maybeToList mttype
      guard $ ttype == target
      return $ noShrink n (mapTerm Just fromJust t)
    `mplus`
    case t of
      Var _     -> mzero
      Lam tt f  -> subTerms n target (f Nothing)
      App t1 t2 ->
        subTerms n target t1
        `mplus`
        subTerms n target t2
    where
    mttype = termWF'm $
      mapTerm (\x -> Just (x, 0)) (fmap $ frbd (Free . fst) (Bound . fst)) t

  replaceWithSubTerms :: Int ->
    Term v (Maybe (Type v, Int)) (Maybe (FrBd (Type v, (w, [Type v])) (Type v, Int))) ->
    [[w'] -> Term v w' (FrBd (w, [Type v]) w')]
  replaceWithSubTerms n t =
    case t of
      Var _  -> mzero
      Lam tt f      -> do
        t' <- replaceWithSubTerms (n + 1) (f $ Just (tt, n))
        return $ \l -> Lam tt $ \x -> t' (x:l)
      App t1 t2     ->
        do
          t1' <- replaceWithSubTerms n t1
          return $ \l -> App (t1' l) (noShrink n (mapTerm Just fromJust t2) l)
        `mplus`
        do
          t2' <- replaceWithSubTerms n t2
          return $ \l -> App (noShrink n (mapTerm Just fromJust t1) l) (t2' l)
    `mplus`
      tail (subTerms n ttype t)
    where
    Just ttype = termWF's $ mapTerm (\x -> Just (x, 0)) (frbd fst fst . fromJust) t

  betaReduce :: Int ->
    (forall w1. Term v w1 (FrBd (FrBd (Type v, (w, [Type v])) (Type v, Int)) w1)) ->
    [[w'] -> Term v w' (FrBd (w, [Type v]) w')]
  betaReduce n t =
    case t of
      Var _    -> mzero
      Lam tt _ -> do
        b <- betaReduce (n + 1) $ boundToFree f (Bound (tt, n))
        return $ \l -> Lam tt $ \x -> b (x:l)
        where
        Lam _ f = t
      App _ _  -> do
        b1 <- betaReduce n t1
        return (\l -> App (b1 l) (noShrink' n t2 l))
        `mplus`  do
        b2 <- betaReduce n t2
        return (\l -> App (noShrink' n t1 l) (b2 l))
        `mplus`  do
        case t1 of
          Lam _ _ ->
              return $ noShrink' n $
                joinFree $ boundToFree
                  (case mapFree (Var . Free) t of (App (Lam _ f) _) -> f)
                  t2
          _       -> mzero
        where
        App t1 t2 = t

  noShrink' :: Int ->
    (forall w1. Term v w1 (FrBd (FrBd (Type v, (w, [Type v])) (Type v, Int)) w1)) ->
    [w'] -> Term v w' (FrBd (w, [Type v]) w')
  noShrink' n t = case t of
    Var (Free (Free (_, x)))  -> \l -> Var (Free x)
    Var (Free (Bound (_, m))) -> \l -> Var (Bound $ l !! (n - 1 - m))
    Var (Bound _) -> impossibleCase x
      where
      x :: forall w1. w1
      Var (Bound x) = t
    Lam tt _                  -> \l ->
      Lam tt $ \x -> noShrink' (n + 1)
        (boundToFree (case t of Lam _ f -> f) (Bound (tt, n))) (x:l)
    App _ _                   -> \l ->
      App (noShrink' n t1 l) (noShrink' n t2 l)
      where
      App t1 t2 = t

shrinkCTerm2 :: forall v. Eq v => [Int] -> CTerm v -> [CTerm v]
shrinkCTerm2 forbid (CTerm l f) = map (\n -> CTerm l (\vl -> candidates vl!!n)) [0..len - 1]
  where
  candidates :: [w] -> [Term v w' (FrBd (w, [Type v]) w')]
  candidates vs = shrinkAux
        forbid
        (zip l vs)
        (mapTerm id
          (frbd (Free . (\((t, v), tl) -> (tApply' t tl, (v, tl)))) Bound)
          (f (zip l vs)))
  -- We can find out the length using () because of parametricity
  len = length $ candidates (repeat ())

{-
unify :: TYPE -> TYPE -> Maybe [(Int, Type Int)]
unify (TYPE n p) (TYPE m q) =
  solve [(p [0..n-1], q [n..n+m-1])] []
  where
  solve :: [(Type Int, Type Int)] -> [(Int, Type Int)] -> Maybe [(Int, Type Int)]
  solve [] l = Just l
  solve ((t@(TVar v), u):sx) l =
    if t == u
      then solve sx l
      else
        if occurs v u then Nothing
          else elim v u sx l
  solve ((u, t@(TVar v)):sx) l =
    elim v u sx l
  solve ((t@(TCon _), u):sx) l =
    if t == u
      then solve sx l
      else Nothing
  solve (((TApp t1 t2), (TApp u1 u2)):sx) l =
    solve ((t1,u1):(t2,u2):sx) l
  solve _ _ = Nothing
  elim v u sx l =
    solve (map (\(t1, t2) -> (subst v u t1, subst v u t2)) sx) ((v, u):(map (\(n, t) -> (n, subst v u t)) l))
  occurs v (TVar v') = v == v'
  occurs v (TCon _) = False
  occurs v (TApp t1 t2) = occurs v t1 || occurs v t2
  subst v t t' = do
    w <- t'
    if w == v
      then t
      else return w

-}
