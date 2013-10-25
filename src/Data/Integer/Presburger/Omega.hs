module Data.Integer.Presburger.Omega where

import Data.Integer.Presburger.Term
import           Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.Ord(comparing)
import Data.List(sortBy,partition)
import Control.Applicative
import Control.Monad

import Debug.Trace

newtype S a = S (RW -> (a,RW))

instance Functor S where
  fmap = liftM

instance Applicative S where
  pure  = return
  (<*>) = ap

instance Monad S where
  return a      = S (\s -> (a,s))
  S m >>= k     = S (\s -> let (a,s1) = m s
                               S m1   = k a
                           in m1 s1)

updS_ :: (RW -> RW) -> S ()
updS_ f = S (\s -> ((), f s))

updS :: (RW -> (a,RW)) -> S a
updS f = S f

newVar :: S Name
newVar = updS $ \rw -> (nameSource rw, rw { nameSource = nameSource rw - 1 })

testRun (S m) = m RW { nameSource = -1, inerts = noInerts, todo = [] }



data Ct = Term :=: Term | Term :<: Term | Ct :\/: Ct
          deriving Show


data RW = RW { nameSource :: !Int
             , inerts     :: Inerts
             , todo       :: [Ct]
             } deriving Show

data Inerts = Inerts
  { upperBounds :: IntMap (Integer,Term)    -- a |-> (c,t)  <=>  c*a < t
  , lowerBounds :: IntMap (Integer,Term)    -- a |-> (c,t)  <=>  t < c*a
  , solved      :: IntMap Term  -- idempotent subst
  } deriving Show

noInerts :: Inerts
noInerts = Inerts { upperBounds = Map.empty
                  , lowerBounds = Map.empty
                  , solved      = Map.empty
                  }

-- Assumes substitution has already been applied
addSolved :: Name -> Term -> S ()
addSolved x t = updS_ $ \rw ->
  let i = inerts rw
      (kickedOutU, otherU) = Map.partitionWithKey kickOut (upperBounds i)
      (kickedOutL, otherL) = Map.partitionWithKey kickOut (lowerBounds i)

  in rw { inerts =
            Inerts { upperBounds = otherU
                   , lowerBounds = otherL
                   , solved = Map.insert x t $ Map.map (tLet x t) $ solved i
                   }
        , todo = cvt       (:<:)  kickedOutU ++
                 cvt (flip (:<:)) kickedOutL ++
                 todo rw
        }
  where
  kickOut y (_,s) = x == y || tHasVar x s

  toC f (y,(c,s)) = if x == y then f (c |*| t)      (tLet x t s)
                              else f (c |*| tVar y) (tLet x t s)
  cvt f           = map (toC f) . Map.toList


-- Assumes substitution has already been applied
-- c + xs = 0
addEq :: Integer -> [(Name,Integer)] -> S ()

addEq 0 []        = return ()

addEq _ []        = fail "impossible" -- XXX: do properly

addEq c [(x,xc)]  = case divMod (-c) xc of
                      (q,0) -> addSolved x (fromInteger q)
                      _     -> fail "impossible"

addEq c xs
  | ((x,xc) : ys, zs) <- partition ((1 ==) . abs . snd) xs =
    addSolved x $ let te = T c $ Map.fromList $ ys ++ zs
                  in if xc > 0 then negate te else te

addEq c xs =
  case common (c : map snd xs) of
    Just d  -> addEq (div c d) [ (x, div xc d) | (x,xc) <- xs ]

    -- See page 6 of paper
    Nothing ->
      do let (x,cx) : rest = sortBy (comparing snd) xs
             m             = abs cx + 1
         v <- newVar
         let sgn  = signum cx
             soln = sum $ (negate sgn * m) |*| tVar v
                        : fromInteger (sgn * modulus c m)
                        : [ (sgn * modulus cy m) |*| tVar y | (y,cy) <- rest ]
         addSolved x soln

         let upd i = div (2*i + m) (2*m) + modulus i m
         addEq (upd c) $ (v, negate (abs cx)) : [ (y, upd cy) | (y,cy) <- rest ]

modulus :: Integer -> Integer -> Integer
modulus a m = a - m * div (2 * a + m) (2 * m)

-- Find a common factor for all the given inputs.
common :: [Integer] -> Maybe Integer
common []  = Nothing
common [x] = Just x
common (x : y : zs) =
  case gcd x y of
    1 -> Nothing
    n -> common (n : zs)



