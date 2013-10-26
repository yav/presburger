module Data.Integer.Presburger.Omega where

import Data.Integer.Presburger.Term
import           Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.Ord(comparing)
import Data.List(sortBy,partition)
import Control.Applicative
import Control.Monad

import Debug.Trace



data Ct = Term :=: Term | Term :<: Term | Ct :\/: Ct
          deriving Show


data RW = RW { nameSource :: !Int
             , inerts     :: Inerts
             , todo       :: [Ct]
             } deriving Show

data Inerts = Inerts
  { upperBounds :: IntMap [(Integer,Term)]  -- a |-> (c,t)  <=>  c*a < t
  , lowerBounds :: IntMap [(Integer,Term)]  -- a |-> (c,t)  <=>  t < c*a
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


-- Assumes variables in the term part are sorted
-- Assumes that substitution has been applied
-- c + xs < 0
addLt c []
  | c < 0     = return ()
  | otherwise = fail "impossible"

addLt c0 xs0 =
  let (c,(y,yc) : ys) =
          case common (c0 : map snd xs0) of
            Just d  -> (div c0 d, [ (x, div xc d) | (x,xc) <- xs0 ])
            Nothing -> (c0, xs0)
  in undefined

-- a * x < alpha  /\ beta < b * x
shadows :: Name -> Integer -> Term -> Term -> Integer -> (Ct,Ct,[Ct])
shadows x a alpha beta b =
  let diff    = b |*| alpha - a |*| beta
      real    = fromInteger 0       :<: diff
      dark    = fromInteger (a * b) :<: diff
      gray = [ (b |*| tVar x) :=: (i |+| beta) | i <- [ 1 .. b - 1 ] ]
  in (real,dark,gray)

-- 2 * x < 1  

-- 2 * x < y
--
-- 1 < x
--
-- shadows a=2 alpha=y beta=1 b=1
--   diff = y - 2
--   real = 0 < y - 2 = 2 < y
--   dark = 2 < y - 2 = 4 < y
--   gray = [ ]


--------------------------------------------------------------------------------

data Answer a = None | One a | Choice (Answer a) (Answer a)
                deriving Show

instance Monad Answer where
  return a           = One a
  fail _             = None
  None >>= _         = None
  One a >>= k        = k a
  Choice m1 m2 >>= k = mplus (m1 >>= k) (m2 >>= k)

instance MonadPlus Answer where
  mzero                = None
  mplus None x         = x
  mplus (Choice x y) z = mplus x (mplus y z)
  mplus x y            = Choice x y

instance Functor Answer where
  fmap = liftM

instance Applicative Answer where
  pure  = return
  (<*>) = ap


newtype S a = S { withS :: RW -> Answer (a,RW) }

instance Monad S where
  return a      = S $ \s -> return (a,s)
  S m >>= k     = S $ \s -> do (a,s1) <- m s
                               let S m1 = k a
                               m1 s1

instance MonadPlus S where
  mzero               = S $ \_ -> mzero
  mplus (S m1) (S m2) = S $ \s -> mplus (m1 s) (m2 s)

instance Functor S where
  fmap = liftM

instance Applicative S where
  pure  = return
  (<*>) = ap


updS_ :: (RW -> RW) -> S ()
updS_ f = S $ \s -> return ((), f s)

updS :: (RW -> (a,RW)) -> S a
updS f = S $ \s -> return (f s)

newVar :: S Name
newVar = updS $ \rw -> (nameSource rw, rw { nameSource = nameSource rw - 1 })

getUBs :: Name -> S [(Integer, Term)]
getUBs x = S $ \rw -> return (Map.findWithDefault [] x (upperBounds rw), rw)

getLBs :: Name -> S [(Integer, Term)]
getLBs x = S $ \rw -> return (Map.findWithDefault [] x (lowerBounds rw), rw)

testRun (S m) = m RW { nameSource = -1, inerts = noInerts, todo = [] }


