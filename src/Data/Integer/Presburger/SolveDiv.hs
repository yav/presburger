module Data.Integer.Presburger.SolveDiv
  ( DivCtr(..), Env, elim
  ) where

import Data.Integer.Presburger.Term
import Data.List(foldl')


-- | A general "divisible by" constraint.
data DivCtr     = Divs !Integer !Term


-- | Given some variables with bounds on them, and a set of
-- "divisible by" constraints, we produce all possible assignments
-- to the variables that are in bounds, and satisfy the constraints.
elim :: Env -> [(Name,Integer)] -> [DivCtr] -> [ Env ]
elim env0 [] ts = if all chk ts then [ env_empty ] else []
  where chk (Divs x t) = divides x (eval_term t env0)
elim env0 ((x,bnd):xs) cs = do let (mb,cs1) = elim_var x cs
                               env <- elim env0 xs cs1
                               v <- case mb of
                                      Nothing -> [ 1 .. bnd ]
                                      Just (NDivides a b t) ->
                                        theorem2 bnd (a,b,eval_term t env)
                               return (env_extend x v env)



-- | "divisible by" constraint on a variable with a coefficient.
data VarDivCtr  = NDivides { divisor  :: !Integer
                           , coeff    :: !Integer
                           , rest     :: !Term
                           }


-- | This theorem combines two "divisible by" contratints on a single
-- variable, into a single constraint on the variable, and a generic
-- "divisible by" constraint that does not mention the variable.
theorem1 :: VarDivCtr -> VarDivCtr -> (VarDivCtr, DivCtr)
theorem1 NDivides { divisor = m, coeff = a1, rest = b1 }
         NDivides { divisor = n, coeff = a2, rest = b2 }
  = (new_x, new_other)

  where (p,q,d)   = extended_gcd (a1 * n) (a2 * m)

        new_x     = NDivides { divisor = m * n
                             , coeff   = d
                             , rest    = (p * n) .* b1 + (q * m) .* b2
                             }

        new_other = Divs d (a2 .* b1 - a1 .* b2)


-- | Repeatedly apply theorem 1 to a set of constraints,
-- to split them into a single constraint on the variable,
-- and additional constraints that do not mention the varibale.
elim_var :: Name -> [DivCtr] -> (Maybe VarDivCtr, [DivCtr])
elim_var x cs = case foldl' part ([],[]) cs of
                  ([], have_not)     -> (Nothing, have_not)
                  (h : hs, have_not) -> let (c,hn) = step h hs have_not
                                        in (Just c,hn)

  where part s@(have,have_not) c@(Divs m t)
          | m == 1      = s -- ignore "divisible by 1" constraints.
          | a == 0      = (have                 , c : have_not)
          | otherwise   = (NDivides m a b : have,     have_not)
            where (a,b) = split_term x t  -- t = a * x + b

        step :: VarDivCtr -> [VarDivCtr] -> [DivCtr] -> (VarDivCtr,[DivCtr])
        step h [] ns      = (h,ns)
        step h (h1:hs) ns = step h2 hs (n : ns)
          where (h2,n) = theorem1 h h1



-- | This theorem produces the solutions for a "divisible by" constraint
-- on a variable, where the "rest" term is a constant.
-- We peoduce only the solutions that are in the range [1 .. bnd]
--
-- solutions for x in [1 .. bnd] of: m | x * a + b
theorem2 :: Integer -> (Integer,Integer,Integer) -> [Integer]
theorem2 bnd (m,a,b)
  | r == 0      = [ t * k - c | t <- [ lower .. upper ] ]
  | otherwise   = []
  where k           = div m d
        c           = p * qu
        (p,_,d)     = extended_gcd a m
        (qu,r)      = divMod b d

        (lower',r1) = divMod (1 + c) k
        lower       = if r1 == 0 then lower' else lower' + 1  -- hmm
        upper       = div (bnd + c) k

  -- lower and upper:
  -- t * k - c = 1   --> t = (1 + c) / k
  -- t * k - c = bnd --> t = (bnd + c) / k




