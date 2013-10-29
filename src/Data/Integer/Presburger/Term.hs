{-# LANGUAGE Safe, PatternGuards #-}
module Data.Integer.Presburger.Term
  ( PP(..)
  , pp
  , Name
  , Term
  , tVar
  , tSplit
  , tSplitVar
  , tCoeff
  , tHasVar
  , isConst
  , tIsOneVar
  , tGetSimpleCoeff
  , tAllCoeffs
  , tFactor
  , tLeastAbsCoeff
  , tLeastVar
  , (|+|)
  , (|*|)
  , tMapCoeff
  , tLet
  , tLetNum
  , tLetNums
  , tVars
  , tVarList
  , tConstPart
  ) where

import qualified Data.IntMap as Map
import           Data.IntMap (IntMap)
import           Data.IntSet (IntSet)
import           Text.PrettyPrint

type Name = Int

-- | The type of terms.  The integer is the constant part of the term,
-- and the `IntMap` maps variables (represented yb @Int@ to their coefficients).
-- The term is a sum of its parts.
-- INVARIANT: the `IntMap` does not map anything to 0.
data Term = T !Integer (IntMap Integer)
              deriving (Eq,Ord)

instance Num Term where
  fromInteger k = T k Map.empty

  x + y
    | Just k <- isConst x = k |+| y
    | Just k <- isConst y = k |+| x

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
    ppVar n | n >= 0    = text ("a" ++ show n)
            | otherwise = text ("b" ++ show (abs n))

-- | Replace a variable with a term.
tLet :: Name -> Term -> Term -> Term
tLet x t1 t2 = let (a,t) = tSplitVar x t2
               in a |*| t1 + t

-- | Replace a variable with a constant.
tLetNum :: Name -> Integer -> Term -> Term
tLetNum x k t = let (c,T n m) = tSplitVar x t
                in T (c * k + n) m

-- | Replace the given variables with constants.
tLetNums :: [(Name,Integer)] -> Term -> Term
tLetNums xs t = foldr (\(x,i) t1 -> tLetNum x i t1) t xs

-- | Construct a term with a single variable.
tVar :: Name -> Term
tVar 0 = error "0 is not a valid varibale name"
tVar x = T 0 (Map.singleton x 1)

infixr 7 |*|

-- | Multiply a term by a constant
(|*|) :: Integer -> Term -> Term
0 |*| _     = fromInteger 0
1 |*| t     = t
k |*| T n m = T (k * n) (fmap (k *) m)

-- | Add a constant, a more efficient version of (+)
(|+|) :: Integer -> Term -> Term
0 |+| t     = t
k |+| T n m = T (k + n) m

-- | Get the coefficient of a term.  Returns 0 if the variable does not occur.
tCoeff :: Name -> Term -> Integer
tCoeff x (T _ m) = Map.findWithDefault 0 x m

-- | Remove a variable from the term, and return its coefficient.
-- If the variable is not present in the term, the coefficient is 0.
tSplitVar :: Name -> Term -> (Integer, Term)
tSplitVar x t@(T n m) =
  case Map.updateLookupWithKey (\_ _ -> Nothing) x m of
    (Nothing,_) -> (0,t)
    (Just k,m1) -> (k, T n m1)

tHasVar :: Name -> Term -> Bool
tHasVar x (T _ m) = Map.member x m

-- | Split into (negative, positive) coeficients.
-- All coeficients in the resulting terms are positive.
tSplit :: Term -> (Term,Term)
tSplit (T k m) =
  let (m1,m2) = Map.partition (> 0) m
      (k1,k2) = if k > 0 then (k,0) else (0,k)
  in (negate (T k2 m2), T k1 m1)

-- | Is this terms just an integer.
isConst :: Term -> Maybe Integer
isConst (T n m)
  | Map.null m  = Just n
  | otherwise   = Nothing

tConstPart :: Term -> Integer
tConstPart (T n _) = n

-- | Returns: @Just (a, b, x)@ if the term is the form: @a + b * x@
tIsOneVar :: Term -> Maybe (Integer, Integer, Name)
tIsOneVar (T a m) = case Map.toList m of
                      [ (x,b) ] -> Just (a, b, x)
                      _         -> Nothing

-- | Returns all coefficient in the term, including the constant as long
-- as it is not 0
tAllCoeffs :: Term -> [Integer]
tAllCoeffs (T a m) = if a == 0 then Map.elems m else a : Map.elems m

-- | Spots terms that contain variables with unit coefficients
-- (i.e., of the form @x + t@ or @t - x@).
-- Returns (coeff, var, rest of term)
tGetSimpleCoeff :: Term -> Maybe (Integer, Name, Term)
tGetSimpleCoeff (T a m) =
  do let (m1,m2) = Map.partition (\x -> x == 1 || x == -1) m
     ((x,xc), m3) <- Map.minViewWithKey m1
     return (xc, x, T a (Map.union m3 m2))

-- | The variables mentioned in this term.
tVars :: Term -> IntSet
tVars (T _ m) = Map.keysSet m

tVarList :: Term -> [Name]
tVarList (T _ m) = Map.keys m


-- | Try to factor-out a common consant (> 1) from a term.
-- For example, @2 + 4x@ becomes @2 * (1 + 2x)@.
tFactor :: Term -> Maybe (Integer, Term)
tFactor (T c m) =
  do d <- common (c : Map.elems m)
     return (d, T (div c d) (fmap (`div` d) m))
  where
  common :: [Integer] -> Maybe Integer
  common []  = Nothing
  common [x] = Just x
  common (x : y : zs) =
    case gcd x y of
      1 -> Nothing
      n -> common (n : zs)

-- | Extract a variable with a coefficient whose absolute value is minimal.
tLeastAbsCoeff :: Term -> Maybe (Integer, Name, Term)
tLeastAbsCoeff (T c m) = do (xc,x,m1) <- Map.foldWithKey step Nothing m
                            return (xc, x, T c m1)
  where
  step x xc Nothing   = Just (xc, x, Map.delete x m)
  step x xc (Just (yc,_,_))
    | abs xc < abs yc = Just (xc, x, Map.delete x m)
  step _ _ it         = it

-- | Extract the least variable from a term
tLeastVar :: Term -> Maybe (Integer, Name, Term)
tLeastVar (T c m) =
  do ((x,xc), m1) <- Map.minViewWithKey m
     return (xc, x, T c m1)

-- | Apply a function to all coefficients, including the constnat
tMapCoeff :: (Integer -> Integer) -> Term -> Term
tMapCoeff f (T c m) = T (f c) (fmap f m)



--------------------------------------------------------------------------------
class PP t where
  ppPrec :: Int -> t -> Doc

pp :: PP t => t -> Doc
pp = ppPrec 0



