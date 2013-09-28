{-# LANGUAGE Safe #-}
module Data.Integer.Presburger
  ( Formula
  , bool, true, false, (/\), (\/), (==>), (<==>), neg, ite, divides
  , (|==|), (|/=|), (|<|), (|<=|), (|>|), (|>=|)
  , forAll, exists
  , fLet

  , Term
  , T.Name, tVar, (|*|), tITE, tLet

  , isTrue, isSat, isValid
  ) where

import qualified Data.Integer.Presburger.Term as T
import qualified Data.Integer.Presburger.Formula as A
import qualified Data.Integer.Presburger.Exists as E
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
bool b = F $ A.fAtom $ A.mkBool b

-- | A true statement.
true :: Formula
true = bool True

-- | A false statement.
false :: Formula
false = bool False

-- | Conjunction.
(/\) :: Formula -> Formula -> Formula
F p /\ F q  = F (A.fConn A.And p q)

-- | Disjunction.
(\/) :: Formula -> Formula -> Formula
F p \/ F q = F (A.fConn A.Or p q)

-- | Implication.
(==>) :: Formula -> Formula -> Formula
p ==> q = neg p \/ q

(<==>) :: Formula -> Formula -> Formula
p <==> q = (p ==> q) /\ (q ==> p)

-- | Negation.
neg :: Formula -> Formula
neg (F fo) = F (A.fNeg fo)

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

-- | Define a variable in a term.
tLet :: T.Name -> Term -> Term -> Term
tLet x (ITE f t e) t1 = tITE f (tLet x t t1) (tLet x e t1)
tLet x t (ITE f t1 e) = tITE f (tLet x t t1) (tLet x t e)
tLet x (T t1) (T t2)  = T (T.tLet x t1 t2)

-- | Define a term-varibale in a formula.
fLet :: T.Name -> Term -> Formula -> Formula
fLet x (T t)       (F fo) = F (A.fLet x t fo)
fLet x (ITE f t e) fo     = ite f (fLet x t fo) (fLet x e fo)

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
atom op (T t1) (T t2) = F $ A.fAtom $ A.mkAtom A.Pos op lhs rhs
  where (lhs,rhs) = T.tSplit (t2 - t1)
atom op (ITE f t1 t2) t = ite f (atom op t1 t) (atom op t2 t)
atom op t (ITE f t1 t2) = ite f (atom op t t1) (atom op t t2)

-- | Assert that the given integer divides the term.
divides :: Integer -> Term -> Formula
divides 0 t = t |==| 0
divides m (T t)         = F $ A.fAtom $ A.mkDiv A.Pos (abs m) t
divides m (ITE f t1 t2) = ite f (divides m t1) (divides m t2)

exists :: [T.Name] -> Formula -> Formula
exists xs (F f) = F (E.exists xs f)

forAll :: [T.Name] -> Formula -> Formula
forAll xs f = neg $ exists xs $ neg f


--------------------------------------------------------------------------------
-- | Check if there is an integer assignment that can make the statement true.
isSat :: Formula -> Bool
isSat f = case isTrue $ exists (Set.toList (freeVars f)) f of
            Just b  -> b
            Nothing -> error "isSat encountered a free variable"
  where freeVars (F fo) = A.freeVars fo

-- | Check if the statement is is for any integer assignment.
isValid :: Formula -> Bool
isValid = not . isSat . neg

isTrue :: Formula -> Maybe Bool
isTrue (F fo) = A.isBool =<< A.isFAtom fo

