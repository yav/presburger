module Data.Integer.Presburger.Omega where

import Data.Integer.Presburger.Term
import           Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.Ord(comparing)
import Data.List(sortBy,partition)
import Control.Applicative
import Control.Monad

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

updS :: (RW -> RW) -> S ()
updS f = S (\s -> ((), f s))


data Ct = Term :=: Term | Term :<: Term | Ct :\/: Ct


data RW = RW { nameSource :: Int
             , inerts     :: Inerts
             , todo       :: [Ct]
             }

data Inerts = Inerts
  { upperBounds :: IntMap (Integer,Term)    -- a |-> (c,t)  <=>  c*a < t
  , lowerBounds :: IntMap (Integer,Term)    -- a |-> (c,t)  <=>  t < c*a
  , solved      :: IntMap Term  -- idempotent subst
  }

-- Assumes substitution has already been applied
addSolved :: Name -> Term -> S ()
addSolved x t = updS $ \rw ->
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
addEq t1 t2 =
  let T c xsMap = t1 - t2
      xs        = Map.toList xsMap
  in cases c xs

  where
  cases 0 []  = return ()
  cases _ []  = fail "impossible" -- XXX: do properly
  cases c [(x,xc)]  = case divMod (-c) xc of
                        (q,0) -> addSolved x (fromInteger q)
                        _     -> fail "impossible"
  cases c xs
    | ((x,xc) : ys, zs) <- partition ((1 ==) . abs . snd) xs =
      addSolved x $ let te = T c $ Map.fromList $ ys ++ zs
                    in if xc > 0 then negate te else te

  cases c xs
    | Just d <- common (c : map snd xs) =
      addEq (T (div c d) (Map.fromList [ (x, div xc d) | (x,xc) <- xs ])) 0


{-
-- 2*x + 3*y = 0
solveEq c xs = undefined
  where
  (x,cx) : rest = sortBy (comparing snd) (Map.toList xs)
  m = abs cx + 1
  modulus a = a - m * (div (2 * a + m) (2 * m))
-}


common :: [Integer] -> Maybe Integer
common []  = Nothing
common [x] = Just x
common (x : y : zs) =
  case gcd x y of
    1 -> Nothing
    n -> common (n : zs)
