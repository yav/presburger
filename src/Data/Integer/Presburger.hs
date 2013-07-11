{-# LANGUAGE Safe #-}
module Data.Integer.Presburger
  ( Formula
  , true, false, (/\), (\/), (==>), neg, ite
  , (|==|), (|/=|), (|<|), (|<=|), (|>|), (|>=|)

  , Term
  , T.Name, tVar, (|*|), tITE

  , checkSat, prove
  ) where

import qualified Data.Integer.Presburger.Term as T
import           Data.Integer.Presburger.Atom
import           Data.Integer.Presburger.JList1
import           Data.IntSet (IntSet)
import qualified Data.IntSet as Set


infixr 1 ==>
infixr 2 \/
infixr 3 /\
infix  4 |==|, |/=|, |<|, |<=|, |>|, |>=|

-- | First-order formulas without quantifiers.
data Formula  = Fo Skeleton (JList Atom)

instance Show Formula where
  show x = show (norm x)

data Skeleton = And Skeleton Skeleton | Or Skeleton Skeleton | Prim
                deriving Show

data Term     = T T.Term
              | ITE Formula Term Term
                deriving Show

-- For printing
data FF = FFAnd [FF] | FFOr [FF] | FFAtom Atom
            deriving Show


norm :: Formula -> FF
norm (Fo s j) = step s j
  where
  step (And s1 s2) (Two as1 as2) = ffAnd (step s1 as1) (step s2 as2)
  step (Or s1 s2)  (Two as1 as2) = ffOr  (step s1 as1) (step s2 as2)
  step Prim        (One a)       = FFAtom a
  step _           _             = error "Malformed formula"

  ffAnd (FFAnd xs) (FFAnd ys) = FFAnd (xs ++ ys)
  ffAnd x y                   = FFAnd [x,y]

  ffOr (FFOr xs) (FFOr ys)    = FFOr (xs ++ ys)
  ffOr x y                    = FFOr [x,y]


instance Num Term where
  fromInteger n   = T (fromInteger n)
  (+)             = tBin (+)
  (-)             = tBin (-)
  (*)             = tBin (*)
  abs x           = tITE (x |>=| 0) x (negate x)
  signum x        = tITE (x |<| 0) (-1) (tITE (x |>| 0) 1 x)

-- For lifting binary operations
tBin :: (T.Term -> T.Term -> T.Term) -> Term -> Term -> Term
tBin f (T x) (T y)     = T (f x y)
tBin f (ITE p t1 t2) t = ITE p (tBin f t1 t) (tBin f t2 t)
tBin f t (ITE p t1 t2) = ITE p (tBin f t t1) (tBin f t t2)

-- | A true statement.
true :: Formula
true = Fo Prim (One (Bool True))

-- | A false statement.
false :: Formula
false = Fo Prim (One (Bool False))

-- | Conjunction.
(/\) :: Formula -> Formula -> Formula
Fo s1 as1 /\ Fo s2 as2 = Fo (And s1 s2) (Two as1 as2)


-- | Disjunction.
(\/) :: Formula -> Formula -> Formula
Fo s1 as1 \/ Fo s2 as2 = Fo (Or s1 s2) (Two as1 as2)

-- | Implication.
(==>) :: Formula -> Formula -> Formula
p ==> q = neg p \/ q

-- | Negation.
neg :: Formula -> Formula
neg (Fo s as) = Fo (negS s) (fmap negA as)
  where
  negS Prim        = Prim
  negS (And s1 s2) = Or  (negS s1) (negS s2)
  negS (Or  s1 s2) = And (negS s1) (negS s2)

  negA (Bool b)          = Bool (not b)
  negA (Atom op lhs rhs) = Atom newOp lhs rhs
    where newOp = case op of
                    Eq  -> Neq
                    Neq -> Eq
                    Lt  -> Geq
                    Leq -> Gt
                    Gt  -> Leq
                    Geq -> Lt

-- | If-then-else.
ite :: Formula -> Formula -> Formula -> Formula
ite p t e = (p /\ t) \/ (neg p /\ e)

-- | Multiple a term by a constant
(|*|) :: Integer -> Term -> Term
k |*| T t = T (k T.|*| t)
k |*| ITE f t1 t2 = ITE f (k |*| t1) (k |*| t2)

-- | A term variable
tVar :: T.Name -> Term
tVar x = T (T.tVar x)

-- | If-then-else term
tITE :: Formula -> Term -> Term -> Term
tITE = ITE

-- | Assert that terms are the same.
(|==|) :: Term -> Term -> Formula
t1 |==| t2 = atom Eq  t1 t2

-- | Assert that terms are different.
(|/=|) :: Term -> Term -> Formula
t1 |/=| t2 = atom Neq t1 t2

-- | Assert that the first term is strictly smaller.
(|<|) :: Term -> Term -> Formula
t1 |<|  t2 = atom Lt  t1 t2

-- | Assert that the first term is smaller than or equal to the second one.
(|<=|) :: Term -> Term -> Formula
t1 |<=| t2 = atom Leq t1 t2

-- | Assert that the first term is strictly greater than the second.
(|>|) :: Term -> Term -> Formula
t1 |>| t2 = atom Gt  t1 t2

-- | Assert that the first term is greater than or equal to the second.
(|>=|) :: Term -> Term -> Formula
t1 |>=| t2 = atom Geq t1 t2

atom :: Op -> Term -> Term -> Formula
atom op (T t1) (T t2) = Fo Prim (One (Atom op lhs rhs))
  where (lhs,rhs) = T.tSplit (t2 - t1)
atom op (ITE f t1 t2) t = ite f (atom op t1 t) (atom op t2 t)
atom op t (ITE f t1 t2) = ite f (atom op t t1) (atom op t t2)


assign :: Skeleton -> JList Bool -> Bool
assign s bs0 = go s bs0
  where
  go Prim        (One b)     = b
  go (And f1 f2) (Two xs ys) = go f1 xs && go f2 ys
  go (Or  f1 f2) (Two xs ys) = go f1 xs || go f2 ys
  go _ _                     = error "shape mismatch in `assign`"


-- | Check if the formula is satisfiable, which means that there are
-- integers that can be assigned to the free varaibles so that
-- the statement becomes true.
checkSat :: Formula -> Bool
checkSat (Fo (Or f1 f2) (Two as1 as2)) = checkSat (Fo f1 as1) ||
                                         checkSat (Fo f2 as2)
checkSat (Fo s as) =
  let vs = fold Set.union $ fmap aVars as
      fs = exists (Set.toList vs) (F [] as [])
      ss = concatMap check fs
  in any (assign s) ss

-- | Check if a formula is valid, which means that it is true no matter
-- what integers we choose for the free variables.
prove :: Formula -> Bool
prove f = not (checkSat (neg f))

aVars :: Atom -> IntSet
aVars (Bool _)         = Set.empty
aVars (Atom _ lhs rhs) = Set.union (T.tVars lhs) (T.tVars rhs)


