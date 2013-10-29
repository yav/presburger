{-# LANGUAGE PatternGuards #-}
module Data.Integer.Presburger.Omega where

import Data.Integer.Presburger.Term
import           Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.List(partition)
import Data.Maybe(maybeToList)
import Control.Applicative
import Control.Monad


--------------------------------------------------------------------------------
-- Solver interface

assertEq :: Term -> Term -> S ()
assertEq t1 t2 =
  do i <- get inerts
     addWork qZeroTerms $ iApSubst i (t1 - t2)

assertLt :: Term -> Term -> S ()
assertLt t1 t2 =
  do i <- get inerts
     addWork qNegTerms $ iApSubst i (t1 - t2)



--------------------------------------------------------------------------------

data RW = RW { nameSource :: !Int
             , todo       :: WorkQ
             , inerts     :: Inerts
             } deriving Show

solveAll :: S ()
solveAll =
  do mbEq <- getWork qZeroTerms
     case mbEq of
       Just p  -> solveIs0 p >> solveAll
       Nothing ->
         do mbLt <- getWork qNegTerms
            case mbLt of
              Just p  -> solveIsNeg p >> solveAll
              Nothing -> return ()


--------------------------------------------------------------------------------
-- The work queue

data WorkQ = WorkQ { zeroTerms     :: [Term]    -- ^ t == 0
                   , negTerms      :: [Term]    -- ^ t <  0
                   } deriving Show

qEmpty :: WorkQ
qEmpty = WorkQ { zeroTerms = [], negTerms = [] }

qLet :: Name -> Term -> WorkQ -> WorkQ
qLet x t q = WorkQ { zeroTerms      = map (tLet x t) (zeroTerms q)
                   , negTerms       = map (tLet x t) (negTerms  q)
                   }

type Field t = (WorkQ -> [t], [t] -> WorkQ -> WorkQ)

qZeroTerms :: Field Term
qZeroTerms = (zeroTerms, \a q -> q { zeroTerms = a })

qNegTerms :: Field Term
qNegTerms = (negTerms, \a q -> q { negTerms = a })

--------------------------------------------------------------------------------
-- Constraints

ctLt :: Term -> Term -> Term
ctLt t1 t2 = t1 - t2

ctGt :: Term -> Term -> Term
ctGt t1 t2 = ctLt t2 t1

--------------------------------------------------------------------------------
-- Inert set

-- | The inert contains the solver state on one possible path.
data Inerts = Inerts
  { bounds :: IntMap ([(Integer,Term)], [(Integer,Term)])
    -- ^ Known lower and upper bounds for variables.
    -- Each entry @(c,t)@ in the first list asserts @t < c * x@
    -- Each entry @(c,t)@ in the second list asserts @c * x < t@

  , solved :: IntMap Term
    -- ^ Definitions for resolved variabless.
    -- These form an idempotent substitution.
  } deriving Show


-- | An empty inert set.
iNone :: Inerts
iNone = Inerts { bounds = Map.empty
               , solved = Map.empty
               }

-- | Rewrite a term using the definitions from an inert set.
iApSubst :: Inerts -> Term -> Term
iApSubst i t = foldr apS t $ Map.toList $ solved i
  where apS (x,t1) t2 = tLet x t1 t2

-- | Add a definition.  Upper and lower bound constraints that mention
-- the variable are "kicked-out" so that they can be reinserted in the
-- context of the new knowledge.
--
--    * Assumes substitution has already been applied.
--
--    * The kciked-out constraints are NOT rewritten, this happens
--      when they get inserted in the work queue.

iSolved :: Name -> Term -> Inerts -> ([Term], Inerts)
iSolved x t i =
  ( kickedOut
  , Inerts { bounds = otherBounds
           , solved = Map.insert x t $ Map.map (tLet x t) $ solved i
           }
  )
  where
  (kickedOut, otherBounds) =

    let (mb, mp1) = Map.updateLookupWithKey (\_ _ -> Nothing) x (bounds i)

        check (c,t1) if tHasVar x t1 then Right 

        upd y (lbs,ubs) = let (lbsStay, lbsKick) = partition stay lbs
                              (ubsStay, ubsKick) = partition stay ubs
                          in ( (lbsStay,ubsStay)
                             , [ 

        -- xy * y < t(x)
        mp2       = fmap (partition (tHasVar x . snd)) mp1

    in ( [ ct | (lbs,ubs) <- maybeToList mb
              ,  ct <- [ ctLt lb (c |*| t) | (c,lb) <- lbs ] ++
                       [ ctLt (c |*| t) ub | (c,ub) <- ubs ]
         ] ++

         [      (y, (lbs,ubs)) <- Map.toList mp1
         , 

         ]



      ++ [ f (yc |*| tVar y) (tLet x t t1) | (y,(vs,_)) <- Map.toList mp2,
                                             (yc,t1)    <- vs ]
       , Map.filter (not . null) (fmap snd mp2)
       )


--------------------------------------------------------------------------------
-- Solving constraints

-- | Solve a constraint if the form @t = 0@.
-- Assumes substitution has already been applied.
solveIs0 :: Term -> S ()
solveIs0 t

  -- A == 0
  | Just a <- isConst t = guard (a == 0)

  -- A + B * x = 0
  | Just (a,b,x) <- tIsOneVar t =
    case divMod (-a) b of
      (q,0) -> addDef x (fromInteger q)
      _     -> mzero

  -- x + S = 0
  | Just (xc,x,s) <- tGetSimpleCoeff t =
    addDef x (if xc > 0 then negate s else s)

  -- A * S = 0
  | Just (_, s) <- tFactor t  = addWork qZeroTerms s

  -- See Section 3.1 of paper for details.
  -- We obtain an equivalent formulation but with smaller coefficients.
  | Just (ak,xk,s) <- tLeastAbsCoeff t =
      do let m = abs ak + 1
         v <- newVar
         let sgn  = signum ak
             soln = (negate sgn * m) |*| tVar v
                  + tMapCoeff (\c -> sgn * modulus c m) s
         addDef xk soln

         let upd i = div (2*i + m) (2*m) + modulus i m
         addWork qZeroTerms (negate (abs ak) |*| tVar v + tMapCoeff upd s)

  | otherwise = error "solveIs0: unreachable"

modulus :: Integer -> Integer -> Integer
modulus a m = a - m * div (2 * a + m) (2 * m)


-- | Solve a constraint of the form @t < 0@.
-- Assumes that substitution has been applied
solveIsNeg :: Term -> S ()
solveIsNeg t

  -- A < 0
  | Just a <- isConst t = guard (a < 0)

  -- A * S < 0
  |Just (_,s) <- tFactor t = addWork qNegTerms s

  -- See Section 5.1 of the paper
  | Just (xc,x,s) <- tLeastVar t =

    do ctrs <- if xc < 0
               -- -XC*x + S < 0
               -- S < XC*x
               then do ubs <- getBounds (snd . bounds) x
                       let b    = negate xc
                           beta = s
                       return [ (a,alpha,b,beta) | (a,alpha) <- ubs ]
               -- XC*x + S < 0
               -- XC*x < -S
               else do lbs <- getBounds (fst . bounds) x
                       let a     = xc
                           alpha = negate s
                       return [ (a,alpha,b,beta) | (b,beta) <- lbs ]

      -- See Note [Shadows]
       mapM_ (\(a,alpha,b,beta) ->
          do let real = ctLt (a |*| beta) (b |*| alpha)
                 dark = ctLt (fromInteger (a * b)) (b |*| alpha - a |*| beta)
                 gray = [ b |*| tVar x - i |+| beta | i <- [ 1 .. b - 1 ] ]
             addWork qNegTerms real
             msum (addWork qNegTerms dark : map (addWork qZeroTerms) gray)
             ) ctrs

      -- XXX: Add constraint!

  | otherwise = error "solveIsNeg: unreachable"


{- Note [Shadows]

  P: beta < b * x
  Q: a * x < alpha

real: a * beta < b * alpha

  beta     < b * x      -- from P
  a * beta < a * b * x  -- (a *)
  a * beta < b * alpha  -- comm. and Q


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


--------------------------------------------------------------------------------
-- Monads

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


newtype S a = S (RW -> Answer (a,RW))

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

updS :: (RW -> (a,RW)) -> S a
updS f = S $ \s -> return (f s)

updS_ :: (RW -> RW) -> S ()
updS_ f = updS $ \rw -> ((),f rw)

get :: (RW -> a) -> S a
get f = updS $ \rw -> (f rw, rw)

newVar :: S Name
newVar = updS $ \rw -> (nameSource rw, rw { nameSource = nameSource rw - 1 })

-- | Try to get a new item from the work queue.
getWork :: Field t -> S (Maybe t)
getWork (getF,setF) = updS $ \rw ->
  let work = todo rw
  in case getF work of
       []     -> (Nothing, rw)
       t : ts -> (Just t,  rw { todo = setF ts work })

-- | Add a new item to the work queue.
addWork :: Field t -> t -> S ()
addWork (getF,setF) t = updS_ $ \rw ->
  let work = todo rw
  in rw { todo = setF (t : getF work) work }

-- | Get upper or lower bounds for a variable.
getBounds :: (Inerts -> IntMap [a]) -> Name -> S [a]
getBounds f x = get $ Map.findWithDefault [] x . f . inerts

-- | Add a new definition.
-- Assumes substitution has already been applied
addDef :: Name -> Term -> S ()
addDef x t = updS_ $ \rw ->
  let (newWork,newInerts) = iSolved x t (inerts rw)
  in rw { inerts = newInerts
        , todo   = qLet x t $
                     let work = todo rw
                     in work { negTerms = newWork ++ negTerms work }
        }


