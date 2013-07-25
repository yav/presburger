{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}
module Data.Integer.Presburger.Div (Solution, DivCt, solve, instTerm) where

import Data.Integer.Presburger.Term
import Data.List(partition)

{- | The extended Euclid's algorithm.
It computes the GCD of two numbres as a linear combination of the inputs.
If @gcd a b = (d, s, t)@, then @d@ is the GCD of a and b,
and @d = s * a + t * b@. -}
gcdE :: Integer -> Integer -> (Integer, Integer, Integer)
gcdE u v = let (d,p,q) = go 1 0 0 1 (abs u) (abs v)
           in (d, signum u * p, signum v * q)

  where
  go !s2 !s1 !t2 !t1 !a !b
    | b == 0      = (a, s2, t2)
    | otherwise   = let (q,r) = divMod a b
                    in go s1 (next q s2 s1) t1 (next q t2 t1) b r

  next q a2 a1 = a2 - q * a1


-- | A solution assigns value to the variables in such a way that
-- all constraints are satisified.
type Solution = [ (Name,Integer) ]

-- | A divisibility constraint.
type DivCt = (Integer, Term)

{- | Given a bunch of upper bounds on some variables, and a collection
of divisibilty constraints, compute the possible values for the variables.
We are only interested in values between 1 and the upper bound (inclusive). -}

solve :: [(Name, Integer)] -> [(Integer, Term)] -> [[(Name, Integer)]]
solve xs cs = solve' xs cs


solve' :: [(Name, Integer)] -> [DivCt] -> [[(Name, Integer)]]
solve' vs [] = go vs
  where
  go ((x,u) : rest) = [ (x,v) : su | su <- go rest, v <- [ 1 .. u ] ]
  go []             = [ [] ]

solve' [] cs
  | all ok cs = [ [] ]
  | otherwise = []
  where
  ok (m,t) = let Just b = isConst t
             in mod b m == 0

solve' ((x,u) : vars) cs =
  [ (x,v) : su | su <- solve' vars rest, v <- soln su ]
  where
  (cs_this, cs_more) = partition ((/= 0) . tCoeff x . snd) cs
  ((m,t),rest0) = joinCts x cs_this

  rest = cs_more ++ rest0

  soln su =
    let (a,t1) = tSplitVar x (instTerm su t)
        Just b = isConst t1
    in solveDiv u m a b

instTerm :: Solution -> Term -> Term
instTerm [] ty = ty
instTerm ((y,n) : more) ty = instTerm more (tLetNum y n ty)

{- | Join a (non-empty) list of constraints into a single constraint
involvong the variable, and a bunch of other constraints that do not. -}
joinCts :: Name -> [DivCt] -> (DivCt, [DivCt])
joinCts x cs = go cs []
  where
  go (c1 : c2 : more) others  = let (cX, other) = joinCts2 x c1 c2
                                in go (cX : more) (other : others)
  go [c1] others              = (c1, others)
  go _ _                      = error "JoinCts: []"


{- Given two constraints involving a variable, @x@, combine them into a
single constraint on that variable and another one that does not mention it.

The first component of the result mentions @x@ but the second does not.
-}
joinCts2 :: Name -> DivCt -> DivCt -> (DivCt, DivCt)
joinCts2 x (m, t1) (n, t2) =
  let (a,b)   = tSplitVar x t1
      (a',b') = tSplitVar x t2
      (d,p,q) = gcdE (a * n) (a' * m)
  in ( ( m * n, d |*| tVar x + (p * n) |*| b + (q * m) |*| b' )
     , ( d,     a' |*| b - a |*| b' )
     )



{- | The solutions for @m | (a * x + b)@, where @x `elem` [ 1 .. u ]@.
We assume that @m > 0@.

The solutions are of the form:

>  do let (d,p,_) = gcdE a m
>     guard (mod b d == 0)
>     [ (-p) * div b d + t * div m d | t <- all_integers ]

Note the @div m d@ is always positive, so we start from an initial
value computed from the lower bound, 1, and then keep incrementing
until we exceed the upper bound.
-}
solveDiv :: Integer -> Integer -> Integer -> Integer -> [Integer]
solveDiv u m a b
  | d == 0    = error ("SOLVEDIV 0: " ++ show (m,a,b))
  | r1 == 0   = takeWhile (<= u) $ iterate (step +) $ t0 * step - extra
  | otherwise = []
  where
  (d,p,_) = gcdE a m
  (k1,r1) = divMod b d
  step    = div m d
  extra   = p * k1
  t0      = case divMod (1 + extra) step of
              (q,r) -> if r == 0 then q else q + 1

_checkSolveDiv :: Integer -> Integer -> Integer -> Integer ->
                                            Maybe ([Integer],[Integer])
_checkSolveDiv u m a b =
  if proposed == correct then Nothing else Just (correct,proposed)
  where
  correct  = [ x | x <- [ 1 .. u ], (a * x + b) `mod` m == 0 ]
  proposed = solveDiv u m a b



_checkSolve :: [(Name,Integer)] -> [DivCt] -> Bool
_checkSolve xs cts = all valid slns && all (`elem` slns) allSlns
  where
  slns = solve xs cts

  valid sln        = all (checkCt sln) cts

  checkCt su (m,t) = case isConst (instTerm su t) of
                       Just k | mod k m == 0  -> True
                       _                       -> False

  allSlns = filter valid (solve xs [])


