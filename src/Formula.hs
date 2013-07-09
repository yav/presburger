{-# LANGUAGE Safe #-}
module Formula
  ( Formula
  , true, false, (/\), (\/), (==>), neg
  , (|==|), (|/=|), (|<|), (|<=|), (|>|), (|>=|)

  , Term
  , Name, tVar, (|*|)

  , checkSat
  ) where

import Term
import Atom
import JList1
import           Data.IntSet (IntSet)
import qualified Data.IntSet as Set


infixr 2 \/
infixr 3 /\
infix  4 |==|, |/=|, |<|, |<=|, |>|, |>=|

-- | First-order formulas without quantifiers.
data Formula  = Fo Skeleton (JList Atom)
data Skeleton = And Skeleton Skeleton | Or Skeleton Skeleton | Prim

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
t1 |>|  t2 = atom Gt  t1 t2

-- | Assert that the first term is greater than or equal to the second.
(|>=|) :: Term -> Term -> Formula
t1 |>=| t2 = atom Geq t1 t2

atom :: Op -> Term -> Term -> Formula
atom op t1 t2 = Fo Prim (One (Atom op lhs rhs))
  where (lhs,rhs) = tSplit (t2 - t1)



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
  in or [ assign s su | su <- ss ]

aVars :: Atom -> IntSet
aVars (Bool _)         = Set.empty
aVars (Atom _ lhs rhs) = Set.union (tVars lhs) (tVars rhs)


