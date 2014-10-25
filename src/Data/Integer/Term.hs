{-# LANGUAGE Safe #-}
module Data.Integer.Term where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Text.PrettyPrint


data Name = UserName !Int | SysName !Int
            deriving (Read,Show,Eq,Ord)

ppName :: Name -> Doc
ppName (UserName x) = text "u" <> int x
ppName (SysName x)  = text "s" <> int x

toName :: Int -> Name
toName = UserName

fromName :: Name -> Maybe Int
fromName (UserName x) = Just x
fromName (SysName _)  = Nothing




-- | The type of terms.  The integer is the constant part of the term,
-- and the `Map` maps variables (represented by @Int@ to their coefficients).
-- The term is a sum of its parts.
-- INVARIANT: the `Map` does not map anything to 0.
data Term = T !Integer (Map Name Integer)
              deriving (Eq,Ord)

infixl 6 |+|, |-|
infixr 7 |*|

-- | A constant term.
tConst :: Integer -> Term
tConst k = T k Map.empty

-- | Construct a term with a single variable.
tVar :: Name -> Term
tVar x = T 0 (Map.singleton x 1)

(|+|) :: Term -> Term -> Term
T n1 m1 |+| T n2 m2 = T (n1 + n2)
                    $ if Map.null m1 then m2 else
                      if Map.null m2 then m1 else
                      Map.filter (/= 0) $ Map.unionWith (+) m1 m2

(|*|) :: Integer -> Term -> Term
0 |*| _     = tConst 0
1 |*| t     = t
k |*| T n m = T (k * n) (fmap (k *) m)

tNeg :: Term -> Term
tNeg t = (-1) |*| t

(|-|) :: Term -> Term -> Term
t1 |-| t2 = t1 |+| tNeg t2


-- | Replace a variable with a term.
tLet :: Name -> Term -> Term -> Term
tLet x t1 t2 = let (a,t) = tSplitVar x t2
               in a |*| t1 |+| t

-- | Replace a variable with a constant.
tLetNum :: Name -> Integer -> Term -> Term
tLetNum x k t = let (c,T n m) = tSplitVar x t
                in T (c * k + n) m

-- | Replace the given variables with constants.
tLetNums :: [(Name,Integer)] -> Term -> Term
tLetNums xs t = foldr (\(x,i) t1 -> tLetNum x i t1) t xs




instance Show Term where
  showsPrec c t = showsPrec c (show (ppTerm t))

ppTerm :: Term -> Doc
ppTerm (T k m) =
  case Map.toList m of
    [] -> integer k
    xs | k /= 0 -> hsep (integer k : map ppProd xs)
    x : xs      -> hsep (ppFst x   : map ppProd xs)

  where
  ppFst (x,1)   = ppName x
  ppFst (x,-1)  = text "-" <> ppName x
  ppFst (x,n)   = ppMul n x

  ppProd (x,1)  = text "+" <+> ppName x
  ppProd (x,-1) = text "-" <+> ppName x
  ppProd (x,n) | n > 0      = text "+" <+> ppMul n x
               | otherwise  = text "-" <+> ppMul (abs n) x

  ppMul n x = integer n <+> text "*" <+> ppName x

-- | Remove a variable from the term, and return its coefficient.
-- If the variable is not present in the term, the coefficient is 0.
tSplitVar :: Name -> Term -> (Integer, Term)
tSplitVar x t@(T n m) =
  case Map.updateLookupWithKey (\_ _ -> Nothing) x m of
    (Nothing,_) -> (0,t)
    (Just k,m1) -> (k, T n m1)

-- | Does the term contain this varibale?
tHasVar :: Name -> Term -> Bool
tHasVar x (T _ m) = Map.member x m

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

-- | Spots terms that contain variables with unit coefficients
-- (i.e., of the form @x + t@ or @t - x@).
-- Returns (coeff, var, rest of term)
tGetSimpleCoeff :: Term -> Maybe (Integer, Name, Term)
tGetSimpleCoeff (T a m) =
  do let (m1,m2) = Map.partition (\x -> x == 1 || x == -1) m
     ((x,xc), m3) <- Map.minViewWithKey m1
     return (xc, x, T a (Map.union m3 m2))

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







