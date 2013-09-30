{-# LANGUAGE Safe #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Integer.Presburger
  ( Formula
  , bool, true, false, (/\), (\/), (==>), (<==>), neg, ite, divides
  , (|==|), (|/=|), (|<|), (|<=|), (|>|), (|>=|)
  , letDivMod
  , nat
  , forAll, bForAll, exists, bExists

  , Term
  , (|*|), tITE

  , isTrue
  ) where

import qualified Data.Integer.Presburger.Term as T
import qualified Data.Integer.Presburger.Formula as A
import qualified Data.Integer.Presburger.Exists as E

infixr 1 ==>
infixr 2 \/
infixr 3 /\
infix  4 |==|, |/=|, |<|, |<=|, |>|, |>=|

-- | First-order formulas
data Formula  = F Int A.Formula -- ^ The Int is the largest bound var in body

instance Show Formula where
  showsPrec p (F _ x) = showsPrec p x

data Term     = T T.Term
              | ITE Formula Term Term
                deriving Show
instance Num Term where
  fromInteger n   = T (fromInteger n)
  (+)             = tBin (+)
  (-)             = tBin (-)
  (*)             = tBin (*)
  abs x           = tITE (x |>=| 0) x (negate x)
  signum x        = tITE (x |<| 0) (-1) (tITE (x |>| 0) 1 0)

-- For lifting binary operations
tBin :: (T.Term -> T.Term -> T.Term) -> Term -> Term -> Term
tBin f (T x) (T y)     = T (f x y)
tBin f (ITE p t1 t2) t = ITE p (tBin f t1 t) (tBin f t2 t)
tBin f t (ITE p t1 t2) = ITE p (tBin f t t1) (tBin f t t2)

-- | A constant formula.
bool :: Bool -> Formula
bool b = F 0 $ A.fAtom $ A.mkBool b

-- | A true statement.
true :: Formula
true = bool True

-- | A false statement.
false :: Formula
false = bool False

-- | Conjunction.
(/\) :: Formula -> Formula -> Formula
F x p /\ F y q    = F (max x y) (A.fConn A.And p q)

-- | Disjunction.
(\/) :: Formula -> Formula -> Formula
F x p \/ F y q = F (max x y) (A.fConn A.Or p q)

-- | Implication.
(==>) :: Formula -> Formula -> Formula
p ==> q = neg p \/ q

(<==>) :: Formula -> Formula -> Formula
p <==> q = (p ==> q) /\ (q ==> p)

-- | Negation.
neg :: Formula -> Formula
neg (F x fo) = F x (A.fNeg fo)

-- | If-then-else.
ite :: Formula -> Formula -> Formula -> Formula
ite p t e = (p /\ t) \/ (neg p /\ e)

-- | Multiple a term by a constant
(|*|) :: Integer -> Term -> Term
k |*| T t = T (k T.|*| t)
k |*| ITE f t1 t2 = ITE f (k |*| t1) (k |*| t2)

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
atom op (T t1) (T t2) = F 0 $ A.fAtom $ A.mkAtom A.Pos op lhs rhs
  where (lhs,rhs) = T.tSplit (t2 - t1)
atom op (ITE f t1 t2) t = ite f (atom op t1 t) (atom op t2 t)
atom op t (ITE f t1 t2) = ite f (atom op t t1) (atom op t t2)

-- | Assert that the given integer divides the term.
divides :: Integer -> Term -> Formula
divides 0 t = t |==| 0
divides m (T t)         = F 0 $ A.fAtom $ A.mkDiv A.Pos (abs m) t
divides m (ITE f t1 t2) = ite f (divides m t1) (divides m t2)

{- | Simluate division and reminder.
@letDivMod t m $ \q r -> p@ asserts that when we divide @t@ by @m@
we get quotiont @q@ and reminder @r@, and also `p` holds. -}

letDivMod :: Term -> Integer -> (Term -> Term -> Formula) -> Formula
letDivMod t m p = exists $ \q r ->
  0 |<=| r /\ r |<| fromInteger m /\ m |*| q + r |==| t /\ p q r


class Quantifiable t where
  quantify :: ([Term] -> Formula -> Formula) -- This is used to tweak the
                                             -- final formula to negate (forall)
                                             -- and assertions about domain
           -> t -> Formula

instance Quantifiable Formula where
  quantify f k = f [] k

instance Quantifiable t => Quantifiable (Term -> t) where
  quantify f p = F name $ E.exists [name] body
    where
    F mx body  = quantify (\xs -> f (term:xs)) $ p term
    term       = T $ T.tVar name
    name       = 1 + mx


exists :: Quantifiable formula => (Term -> formula) -> Formula
exists p = quantify (\_ -> id) p

bExists :: Quantifiable formula => (Term -> Formula) ->
                                     (Term -> formula) -> Formula
bExists dom p = quantify (\ts f -> foldr (/\) f (map dom ts)) p

forAll :: Quantifiable formula => (Term -> formula) -> Formula
forAll p = neg $ quantify (\_ -> neg) p

bForAll :: Quantifiable formula => (Term -> Formula)
                                -> (Term -> formula) -> Formula
bForAll dom p = neg $ quantify (\ts f -> neg $ foldr (==>) f (map dom ts)) p

-- | Assert that a term is a ntural number
nat :: Term -> Formula
nat x = 0 |<=| x

--------------------------------------------------------------------------------
isTrue :: Formula -> Bool
isTrue (F _ fo) = case A.isBool =<< A.isFAtom fo of
                    Just x -> x
                    Nothing -> error "Unexpected free variables in term"

