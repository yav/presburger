{-# LANGUAGE PatternGuards #-}
module Data.Integer.Presburger.Omega where

import Data.Integer.Presburger.Term
import           Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.List(partition)
import Data.Maybe(maybeToList)
import Control.Applicative
import Control.Monad


data RW = RW { nameSource :: !Int
             , todo       :: WorkQ
             , inerts     :: Inerts
             } deriving Show

solveAll :: S ()
solveAll =
  do mbEq <- getIs0
     case mbEq of
       Just p  -> solveIs0 p >> solveAll
       Nothing ->
         do mbLt <- getIsNeg
            case mbLt of
              Just p  -> solveIsNeg p >> solveAll
              Nothing -> return ()




--------------------------------------------------------------------------------
-- The work queue

data WorkQ = WorkQ { zeroTerms :: [Term]    -- ^ t == 0
                   , negTerms  :: [Term]    -- ^ t <  0
                   } deriving Show

qEmpty :: WorkQ
qEmpty = WorkQ { zeroTerms = [], negTerms = [] }

qLet :: Name -> Term -> WorkQ -> WorkQ
qLet x t q = WorkQ { zeroTerms = map (tLet x t) (zeroTerms q)
                   , negTerms  = map (tLet x t) (negTerms  q)
                   }

ctLt :: Term -> Term -> Term
ctLt t1 t2 = t1 - t2

ctGt :: Term -> Term -> Term
ctGt t1 t2 = ctLt t2 t1

--------------------------------------------------------------------------------


data Inerts = Inerts
  { upperBounds :: IntMap [(Integer,Term)]  -- ^ a |-> (c,t)  <=>  c*a < t
  , lowerBounds :: IntMap [(Integer,Term)]  -- ^ a |-> (c,t)  <=>  t < c*a
  , solved      :: IntMap Term              -- ^ a |-> t, idempotent subst
  } deriving Show

noInerts :: Inerts
noInerts = Inerts { upperBounds = Map.empty
                  , lowerBounds = Map.empty
                  , solved      = Map.empty
                  }

-- | Add a simple equality.
-- Assumes substitution has already been applied.
-- Returns: (restarted lessThan0 constraints, and new inerts)
-- The lessThan0 constraints are NOT rewritten.
iSolved :: Name -> Term -> Inerts -> ([Term], Inerts)
iSolved x t i =
  ( kickedOutL ++ kickedOutU
  , Inerts { upperBounds = otherU
           , lowerBounds = otherL
           , solved      = Map.insert x t $ Map.map (tLet x t) $ solved i
           }
  )
  where
  (kickedOutU, otherU) = upd ctLt (upperBounds i)
  (kickedOutL, otherL) = upd ctGt (lowerBounds i)

  upd f mp =
        -- xc * x < t
    let (mb, mp1) = Map.updateLookupWithKey (\_ _ -> Nothing) x mp

        -- xy * y < t(x)
        mp2       = fmap (partition (tHasVar x . snd)) mp1
    in ( [ f (xc |*| t) t1 | (xc,t1) <- concat (maybeToList mb) ]
      ++ [ f (yc |*| tVar y) (tLet x t t1) | (y,(vs,_)) <- Map.toList mp2,
                                             (yc,t1)    <- vs ]
       , Map.filter (not . null) (fmap snd mp2)
       )


-- Assumes substitution has already been applied
addSolved :: Name -> Term -> S ()
addSolved x t = updS_ $ \rw ->
  let (newWork,newInerts) = iSolved x t (inerts rw)
  in rw { inerts = newInerts
        , todo   = qLet x t $
                     let work = todo rw
                     in work { negTerms = newWork ++ negTerms work }
        }

-- Add equality work
is0 :: Term -> S ()
is0 t = updS_ $ \rw -> rw { todo = let work = todo rw
                                   in work { zeroTerms = t : zeroTerms work } }

-- Add non-equality work
isNeg :: Term -> S ()
isNeg t = updS_ $ \rw -> rw { todo = let work = todo rw
                                     in work { negTerms = t : negTerms work } }

-- Assumes substitution has already been applied
-- c + xs = 0
solveIs0 :: Term -> S ()
solveIs0 t

  -- A == 0
  | Just a <- isConst t = guard (a == 0)

  -- A + B * x = 0
  | Just (a,b,x) <- tIsOneVar t =
    case divMod (-a) b of
      (q,0) -> addSolved x (fromInteger q)
      _     -> mzero

  -- x + S = 0
  | Just (xc,x,s) <- tGetSimpleCoeff t =
    addSolved x (if xc > 0 then negate s else s)

  -- K * S = 0
  | Just (_, s) <- tFactor t  = is0 s

  -- See Section 3.1 of paper for details.
  -- We obtain an equivalent formulation but with smaller coefficients.
  | Just (ak,xk,s) <- tLeastAbsCoeff t =
      do let m = abs ak + 1
         v <- newVar
         let sgn  = signum ak
             soln = (negate sgn * m) |*| tVar v
                  + tMapCoeff (\c -> sgn * modulus c m) s
         addSolved xk soln

         let upd i = div (2*i + m) (2*m) + modulus i m
         is0 (negate (abs ak) |*| tVar v + tMapCoeff upd s)

  | otherwise = error "solveIs0: unreachable"

modulus :: Integer -> Integer -> Integer
modulus a m = a - m * div (2 * a + m) (2 * m)


-- Assumes that substitution has been applied
solveIsNeg :: Term -> S ()
solveIsNeg t

  -- A < 0
  | Just a <- isConst t = guard (a < 0)

  -- K * S < 0
  | Just (_,s) <- tFactor t = isNeg s

  -- See Section 5.1 of the paper
  | Just (xc,x,s) <- tLeastVar t =

    if xc < 0
        -- -XC*x + S < 0
        -- S < XC*x
        then do ubs <- getUBs x
                let b    = negate xc
                    beta = s
                addShadows [ shadows x a alpha beta b | (a,alpha) <- ubs ]
        -- XC*x + S < 0
        -- XC*x < -S
        else do lbs <- getLBs x
                let a     = xc
                    alpha = negate s
                addShadows [ shadows x a alpha beta b | (b,beta) <- lbs ]

  | otherwise = error "solveIsNeg: unreachable"

addShadows :: [(S (), S ())] -> S ()
addShadows shs =
  do let (reals,dark_grays) = unzip shs
     sequence_ reals
     sequence_ dark_grays


-- a * x < alpha /\ beta < b * x
shadows :: Name -> Integer -> Term -> Term -> Integer -> (S (), S())
shadows x a alpha beta b =
  let real = ctLt (a |*| beta) (b |*| alpha)
      dark = ctLt (fromInteger (a * b)) (b |*| alpha - a |*| beta)
      gray = [ b |*| tVar x - i |+| beta | i <- [ 1 .. b - 1 ] ]
  in (isNeg real, isNeg dark `mplus` mapM_ is0 gray)


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
  fmap _ None           = None
  fmap f (One x)        = One (f x)
  fmap f (Choice x1 x2) = Choice (fmap f x1) (fmap f x2)

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

get :: (RW -> a) -> S a
get f = S $ \s -> return (f s, s)

newVar :: S Name
newVar = updS $ \rw -> (nameSource rw, rw { nameSource = nameSource rw - 1 })

getUBs :: Name -> S [(Integer, Term)]
getUBs x = get $ Map.findWithDefault [] x . upperBounds . inerts

getLBs :: Name -> S [(Integer, Term)]
getLBs x = get $ Map.findWithDefault [] x . lowerBounds . inerts

getIs0 :: S (Maybe Term)
getIs0 = updS $ \rw ->
  let work = todo rw
  in case zeroTerms work of
       []     -> (Nothing, rw)
       t : ts -> (Just t,  rw { todo = work { zeroTerms = ts } })

getIsNeg :: S (Maybe Term)
getIsNeg = updS $ \rw ->
  let work = todo rw
  in case negTerms work of
       []     -> (Nothing, rw)
       t : ts -> (Just t,  rw { todo = work { negTerms = ts } })


testRun (S m) = m RW { nameSource = -1, inerts = noInerts, todo = qEmpty }

