module Data.Integer.Presburger.Term
  ( Term, Name, split_term, is_constant, (.*), var, num
  , Env, env_empty, env_extend
  , eval_term, subst_term
  , var_name
  , module U
  ) where

import Data.Integer.Presburger.Utils as U

import qualified Data.IntMap as Map
import Data.Maybe(fromMaybe)
import Control.Monad(mplus,guard)


-- | We represent the names of variables in terms as integers.
type Name           = Int

-- | Terms of Presburger arithmetic.
-- Term are created by using the 'Num' class.
-- WARNING: Presburger arithmetic only supports multiplication
-- by a constant, trying to create invalid terms will result
-- in a run-time error.  A more type-safe alternative is to
-- use the '(.*)' operator.
data Term           = Term (Map.IntMap Integer) Integer


-- | @split_term x (n * x + t1) = (n,t1)@
-- @x@ does not occur in @t1@
split_term         :: Name -> Term -> (Integer,Term)
split_term x (Term m n) = (fromMaybe 0 c, Term m1 n)
  where (c,m1) = Map.updateLookupWithKey (\_ _ -> Nothing) x m

var                :: Name -> Term
var x               = Term (Map.singleton x 1) 0

num                :: Integer -> Term
num n               = Term Map.empty n


-- Evaluation ------------------------------------------------------------------
newtype Env = Env (Map.IntMap Integer)

env_empty :: Env
env_empty = Env (Map.empty)

env_extend :: Name -> Integer -> Env -> Env
env_extend x v (Env m) = Env (Map.insert x v m)

-- The meaning of a term with free variables
-- If the term contains free variables that are not defined, then
-- we assume that these variables are 0.
eval_term :: Term -> Env -> Integer
eval_term (Term m k) (Env env) = sum (k : map eval_var (Map.toList m))
  where eval_var (x,c) = case Map.lookup x env of
                           Nothing -> 0
                           Just v  -> c * v

subst_term :: Name -> Integer -> Term -> Term
subst_term x n t = case split_term x t of
                     (c, Term m k) -> Term m (k + c * n)

--------------------------------------------------------------------------------

instance Eq Term where
  t1 == t2  = is_constant (t1 - t2) == Just 0

instance Num Term where
  fromInteger n             = Term Map.empty n

  Term m1 n1 + Term m2 n2   = Term (Map.unionWith (+) m1 m2) (n1 + n2)

  negate (Term m n)         = Term (Map.map negate m) (negate n)

  t1 * t2  = case fmap (.* t2) (is_constant t1) `mplus`
                  fmap (.* t1) (is_constant t2) of
               Just t  -> t
               Nothing -> error $ unlines [ "[(*) @ Term] Non-linear product:"
                                          , "  *** " ++ show t1
                                          , "  *** " ++ show t2
                                          ]
  signum t  = case is_constant t of
                Just n  -> num (signum n)
                Nothing -> error $ unlines [ "[signum @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]

  abs t     = case is_constant t of
                Just n  -> num (abs n)
                Nothing -> error $ unlines [ "[abs @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]


-- | Check if a term is a constant (i.e., contains no variables).
-- If so, then we return the constant, otherwise we return 'Nothing'.
is_constant :: Term -> Maybe Integer
is_constant (Term m n) = guard (all (0 ==) (Map.elems m)) >> return n

(.*) :: Integer -> Term -> Term
0 .* _        = 0
1 .* t        = t
k .* Term m n = Term (Map.map (k *) m) (k * n)


var_name           :: Name -> String
var_name x          = let (a,b) = divMod x 26
                          rest = if a == 0 then "" else show a
                      in toEnum (97 + b) : rest

instance Show Term where show x = show (pp x)
instance PP Term where
  pp (Term m k) | isEmpty vars  = text (show k)
                | k == 0        = vars
                | k > 0         = vars <+> char '+' <+> text (show k)
                | otherwise     = vars <+> char '-' <+> text (show $ abs k)
    where ppvar (x,n) = sign <+> co <+> text (var_name x)
            where (sign,co)
                     | n == -1    = (char '-', empty)
                     | n < 0      = (char '-', text (show (abs n)) <+> char '*')
                     | n == 1     = (char '+', empty)
                     | otherwise  = (char '+', text (show n) <+> char '*')
          first_var (x,1)  = text (var_name x)
          first_var (x,-1) = char '-' <> text (var_name x)
          first_var (x,n)  = text (show n) <+> char '*' <+> text (var_name x)

          vars = case filter ((/= 0) . snd) (Map.toList m) of
                   []     -> empty
                   v : vs -> first_var v <+> hsep (map ppvar vs)


instance PP Env where
  pp (Env e)  = vcat (map sh (Map.toList e))
    where sh (x,y)  = text (var_name x) <+> text "=" <+> text (show y)








