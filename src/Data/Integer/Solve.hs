{-# LANGUAGE Safe #-}
module Data.Integer.Solve where

import Data.Integer.Term
import Control.Monad (ap, liftM)
import Control.Applicative (Applicative(..))

{-
solveIs0 :: Term -> Maybe [ (Name, Term) ]
solveIs0 t = solveIs0' =<< apSubst t
-}

newtype S a = S { runS :: Int -> Maybe (a, Int) }

instance Functor S where fmap = liftM
instance Applicative S where pure = return; (<*>) = ap
instance Monad S where
  return x  = S (\s -> Just (x, s))
  fail _    = impossible
  S m >>= k = S (\s -> case m s of
                         Nothing -> Nothing
                         Just (a,s1) -> let S m1 = k a
                                        in m1 s1)

newVar :: S Name
newVar = S (\s -> let s1 = s + 1
                  in s1 `seq` Just (SysName s, s1))

impossible :: S a
impossible = S (\_ -> Nothing)

-- | Solve a constraint of the form @t = 0@.
solveIs0 :: Term -> S [ (Name, Term) ]
solveIs0 t

  -- A == 0
  | Just a <- isConst t = if (a == 0) then return [] else impossible

  -- A + B * x = 0
  | Just (a,b,x) <- tIsOneVar t =
    case divMod (-a) b of
      (q,0) -> return [ (x, tConst q) ]
      _     -> impossible

  --  x + S = 0
  -- -x + S = 0
  | Just (xc,x,s) <- tGetSimpleCoeff t =
    return [ (x, if xc > 0 then tNeg s else s) ]

  -- A * S = 0
  | Just (_, s) <- tFactor t  = solveIs0 s

  -- See Section 3.1 of paper for details.
  -- We obtain an equivalent formulation but with smaller coefficients.
  | Just (ak,xk,s) <- tLeastAbsCoeff t =
      do let m = abs ak + 1
         v <- newVar
         let sgn  = signum ak
             soln =     (negate sgn * m) |*| tVar v
                    |+| tMapCoeff (\c -> sgn * modulus c m) s

         let upd i = div (2*i + m) (2*m) + modulus i m
         defs <- solveIs0 (negate (abs ak) |*| tVar v |+| tMapCoeff upd s)
         return ((xk,soln) : defs)

  | otherwise = error "solveIs0: unreachable"


modulus :: Integer -> Integer -> Integer
modulus a m = a - m * div (2 * a + m) (2 * m)

{-
test t = fmap fst (runS (solveIs0 t) 0)
v1 : v2 : v3 : _ = map (tVar . toName) [ 0 .. ]
-}



{-
solveIsNeg :: Term -> S ()
solveIsNeg t = solveIsNeg' =<< apSubst t
-}


-- | Solve a constraint of the form @t < 0@.
solveIsNeg :: Term -> S ()
solveIsNeg t

  -- A < 0
  | Just a <- isConst t = if a < 0 then return () else impossible

  -- A * S < 0
  | Just (_,s) <- tFactor t = solveIsNeg s

  -- See Section 5.1 of the paper
  | Just (xc,x,s) <- tLeastVar t =

    do ctrs <- if xc < 0
               -- -XC*x + S < 0
               -- S < XC*x
               then do ubs <- getBounds Upper x
                       let b    = negate xc
                           beta = s
                       addBound Lower x (Bound b beta)
                       return [ (a,alpha,b,beta) | Bound a alpha <- ubs ]
               -- XC*x + S < 0
               -- XC*x < -S
               else do lbs <- getBounds Lower x
                       let a     = xc
                           alpha = tNeg s
                       addBound Upper x (Bound a alpha)
                       return [ (a,alpha,b,beta) | Bound b beta <- lbs ]

      -- See Note [Shadows]
       mapM_ (\(a,alpha,b,beta) ->
          do let real = ctLt (a |*| beta) (b |*| alpha)
                 dark = ctLt (tConst (a * b)) (b |*| alpha |-| a |*| beta)
                 gray = [ ctEq (b |*| tVar x) (tConst i |+| beta)
                                                      | i <- [ 1 .. b - 1 ] ]
             solveIsNeg real
             foldl orElse (solveIsNeg dark) (map solveIs0 gray)
             ) ctrs

  | otherwise = error "solveIsNeg: unreachable"


{- Note [Shadows]

  P: beta < b * x
  Q: a * x < alpha

real: a * beta < b * alpha

show "P & Q ==> real"
proof
  beta     < b * x      -- from P
  a * beta < a * b * x  -- (a *) and a > 0
  a * beta < b * alpha  -- comm. and Q
qed


dark: b * alpha - a * beta > a * b


gray: b * x = beta + 1 \/
      b * x = beta + 2 \/
      ...
      b * x = beta + (b-1)

We stop at @b - 1@ because if:

> b * x                >= beta + b
> a * b * x            >= a * (beta + b)     -- (a *)
> a * b * x            >= a * beta + a * b   -- distrib.
> b * alpha            >  a * beta + a * b   -- comm. and Q
> b * alpha - a * beta > a * b               -- subtract (a * beta)

which is covered by the dark shadow.
-}

