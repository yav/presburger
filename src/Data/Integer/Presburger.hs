{-# LANGUAGE Safe #-}
module Data.Integer.Presburger
  ( Formula
  , bool, true, false, (/\), (\/), (==>), neg, ite
  , (|==|), (|/=|), (|<|), (|<=|), (|>|), (|>=|)
  , forAll, exists

  , Term
  , T.Name, tVar, (|*|), tITE

  , isTrue, isSat, isValid
  ) where

import qualified Data.Integer.Presburger.Term as T
import qualified Data.Integer.Presburger.Atom as A
import           Data.IntSet (IntSet)
import qualified Data.IntSet as Set


infixr 1 ==>
infixr 2 \/
infixr 3 /\
infix  4 |==|, |/=|, |<|, |<=|, |>|, |>=|

-- | First-order formulas
newtype Formula  = F A.Formula

instance Show Formula where
  showsPrec p (F x) = showsPrec p x

data Term     = T T.Term
              | ITE Formula Term Term
                deriving Show
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

-- | A constant formula.
bool :: Bool -> Formula
bool b = F $ A.AtomF $ A.Bool b

-- | A true statement.
true :: Formula
true = bool True

-- | A false statement.
false :: Formula
false = bool False

-- | Conjunction.
(/\) :: Formula -> Formula -> Formula
F p /\ F q  = F (A.ConnF A.And p q)

-- | Disjunction.
(\/) :: Formula -> Formula -> Formula
F p \/ F q = F (A.ConnF A.Or p q)

-- | Implication.
(==>) :: Formula -> Formula -> Formula
p ==> q = neg p \/ q

-- | Negation.
neg :: Formula -> Formula
neg (F fo) = F (negF fo)
  where
  negC A.And                = A.Or
  negC A.Or                 = A.And

  negP A.Pos                = A.Neg
  negP A.Neg                = A.Pos

  negF (A.ConnF c f1 f2)    = A.ConnF (negC c) (negF f1) (negF f2)
  negF (A.AtomF a)          = A.AtomF (negA a)

  negA (A.Bool b)           = A.Bool (not b)
  negA (A.Atom pol op t1 t2)= A.Atom (negP pol) op t1 t2
  negA (A.Div  pol m t)     = A.Div  (negP pol) m t



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
t1 |==| t2 = atom A.Eq  t1 t2

-- | Assert that the first term is strictly smaller.
(|<|) :: Term -> Term -> Formula
t1 |<|  t2 = atom A.Lt  t1 t2

-- | Assert that the first term is smaller than or equal to the second one.
(|<=|) :: Term -> Term -> Formula
t1 |<=| t2 = atom A.Leq t1 t2

-- | Assert that terms are different.
(|/=|) :: Term -> Term -> Formula
t1 |/=| t2 = neg (t1 |==| t2)

-- | Assert that the first term is strictly greater than the second.
(|>|) :: Term -> Term -> Formula
t1 |>| t2 = neg (t1 |<=| t2)

-- | Assert that the first term is greater than or equal to the second.
(|>=|) :: Term -> Term -> Formula
t1 |>=| t2 = neg (t1 |<| t2)

atom :: A.PredS -> Term -> Term -> Formula
atom op (T t1) (T t2) = F $ A.AtomF $ A.Atom A.Pos op lhs rhs
  where (lhs,rhs) = T.tSplit (t2 - t1)
atom op (ITE f t1 t2) t = ite f (atom op t1 t) (atom op t2 t)
atom op t (ITE f t1 t2) = ite f (atom op t t1) (atom op t t2)

exists :: [T.Name] -> Formula -> Formula
exists xs (F f) = F (A.exists xs f)

forAll :: [T.Name] -> Formula -> Formula
forAll xs f = neg $ exists xs $ neg f


--------------------------------------------------------------------------------

freeVars :: Formula -> IntSet
freeVars (F fo0) = freeVarsF fo0
  where
  freeVarsF fo =
    case fo of
      A.ConnF _ f1 f2 -> Set.union (freeVarsF f1) (freeVarsF f2)
      A.AtomF a       -> freeVarsA a

  freeVarsA at =
    case at of
      A.Bool _          -> Set.empty
      A.Div _ _ t       -> T.tVars t
      A.Atom _ _ t1 t2  -> Set.union (T.tVars t1) (T.tVars t2)

-- | Check if there is an integer assignment that can make the statement true.
isSat :: Formula -> Bool
isSat f = case isTrue $ exists (Set.toList (freeVars f)) f of
            Just b  -> b
            Nothing -> error "isSat encountered a free variable"

-- | Check if the statement is is for any integer assignment.
isValid :: Formula -> Bool
isValid = not . isSat . neg

isTrue :: Formula -> Maybe Bool
isTrue (F fo) = A.isTrue fo

