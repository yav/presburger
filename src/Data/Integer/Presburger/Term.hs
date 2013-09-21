{-# LANGUAGE Safe, PatternGuards #-}
module Data.Integer.Presburger.Term where

import qualified Data.IntMap as Map
import           Data.IntMap (IntMap)
import           Data.IntSet (IntSet)
import           Text.PrettyPrint

type Name = Int

-- | The type of terms.  The integer is the constant part of the term,
-- and the `IntMap` maps variables (represented yb @Int@ to their coefficients).
-- The term is a sum of its parts.
-- INVARIANT: the `IntMap` does not map anything to 0.
data Term = T Integer (IntMap Integer)
              deriving (Eq,Ord)

instance Num Term where
  fromInteger k = T k Map.empty

  T n1 m1 + T n2 m2 = T (n1 + n2) $ Map.filter (/= 0) $ Map.unionWith (+) m1 m2

  x - y             = x + negate y

  x * y
    | Just k <- isConst x = k |*| y
    | Just k <- isConst y = k |*| x
    | otherwise           = error "Term: Non-linear multiplication"

  negate x    = (-1) |*| x

  abs x
    | Just k <- isConst x   = fromInteger (abs k)
    | otherwise             = error "Term: `abs` with variables"

  signum x
    | Just k <- isConst x   = fromInteger (signum k)
    | otherwise             = error "Term: `signum` with variables"

instance Show Term where
  showsPrec c t = showsPrec c (ppPrec c t)

instance PP Term where
  ppPrec _ (T k m) =
    case Map.toList m of
      [] -> integer k
      xs | k /= 0 -> hsep (integer k : map ppTerm xs)
      x : xs      -> hsep (ppFst x : map ppTerm xs)

    where
    ppFst (x,1)   = ppVar x
    ppFst (x,-1)  = text "-" <> ppVar x
    ppFst (x,n)   = ppMul n x

    ppTerm (x,1)  = text "+" <+> ppVar x
    ppTerm (x,-1) = text "-" <+> ppVar x
    ppTerm (x,n) | n > 0      = text "+" <+> ppMul n x
                 | otherwise  = text "-" <+> ppMul (abs n) x

    ppMul n x = integer n <+> text "*" <+> ppVar x
    ppVar n   = text ("a" ++ show n)

-- | Replace a variable with a term.
tLet :: Name -> Term -> Term -> Term
tLet x t1 t2 = let (a,t) = tSplitVar x t2
               in a |*| t1 + t

-- | Replace a variable with a constant.
tLetNum :: Name -> Integer -> Term -> Term
tLetNum x k t = let (c,T n m) = tSplitVar x t
                in T (c * k + n) m

-- | Construct a term with a single variable.
tVar :: Name -> Term
tVar x = T 0 (Map.singleton x 1)

infixr 7 |*|

-- | Multiply a term by a constant
(|*|) :: Integer -> Term -> Term
0 |*| _     = fromInteger 0
1 |*| t     = t
k |*| T n m = T (k * n) (fmap (k *) m)

-- | Remove occurances of a variable from the term.
tDrop :: Name -> Term -> Term
tDrop x (T n m) = T n (Map.delete x m)

-- | Get the coefficient of a term.  Returns 0 if the variable does not occur.
tCoeff :: Name -> Term -> Integer
tCoeff x (T _ m) = Map.findWithDefault 0 x m

-- | Remove a variable from the term, and return its coefficient.
tSplitVar :: Name -> Term -> (Integer, Term)
tSplitVar x t@(T n m) =
  case Map.updateLookupWithKey (\_ _ -> Nothing) x m of
    (Nothing,_) -> (0,t)
    (Just k,m1) -> (k, T n m1)

-- | Split into (negative, positive) coeficients.
-- All coeficients in the resulting terms are positive.
tSplit :: Term -> (Term,Term)
tSplit (T k m) =
  let (m1,m2) = Map.partition (> 0) m
      (k1,k2) = if k > 0 then (k,0) else (0,k)
  in (negate (T k2 m2), T k1 m1)

isConst :: Term -> Maybe Integer
isConst (T n m)
  | Map.null m  = Just n
  | otherwise   = Nothing

tVars :: Term -> IntSet
tVars (T _ m) = Map.keysSet m

--------------------------------------------------------------------------------
class PP t where
  ppPrec :: Int -> t -> Doc

pp :: PP t => t -> Doc
pp = ppPrec 0



