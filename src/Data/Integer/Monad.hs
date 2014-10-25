{-# LANGUAGE Safe #-}
module Data.Integer.Monad where

import           Data.Integer.Term
import           Data.Integer.Inerts

import           Control.Monad (ap, liftM)
import           Control.Applicative (Applicative(..))


newtype S a = S { runS :: RW -> Maybe (a, RW) }

data RW = RW { nameSource :: !Int
             , inerts     :: Inerts
             } deriving Show

initRW :: RW
initRW = RW { nameSource = 0, inerts = iNone }


instance Functor S where
  fmap = liftM

instance Applicative S where
  pure = return
  (<*>) = ap

instance Monad S where
  return x  = S (\s -> Just (x, s))
  fail _    = impossible
  S m >>= k = S (\s -> case m s of
                         Nothing -> Nothing
                         Just (a,s1) -> let S m1 = k a
                                        in m1 s1)

updS :: (RW -> (a,RW)) -> S a
updS f = S $ \s -> return (f s)

updS_ :: (RW -> RW) -> S ()
updS_ f = updS $ \rw -> ((),f rw)

get :: (RW -> a) -> S a
get f = updS $ \rw -> (f rw, rw)


-- | Generate a new variable.
newVar :: S Name
newVar = updS $ \rw -> ( SysName (nameSource rw)
                       , rw { nameSource = nameSource rw + 1 }
                       )

-- | We detected a contradiction.
impossible :: S a
impossible = S (\_ -> Nothing)


-- | Get lower or upper bounds for a variable.
getBounds :: BoundType -> Name -> S [Bound]
getBounds f x = get $ \rw -> iBounds f x (inerts rw)

-- | Record a bound for the given variable.
addBound :: BoundType -> Name -> Bound -> S ()
addBound bt x b = updS_ $ \rw -> rw { inerts = iAddBound bt x b (inerts rw) }

-- | Add a new definition.
-- Assumes substitution has already been applied.
-- Returns kicked-out "less-than" constraints.
addDef :: Name -> Term -> S [Term]
addDef x t =
  do newWork <- updS $ \rw -> let (newWork,newInerts) = iSolved x t (inerts rw)
                              in (newWork, rw { inerts = newInerts })
     return newWork

-- | Apply the current substitution to this term.
apSubst :: Term -> S Term
apSubst t =
  do i <- get inerts
     return (iApSubst i t)


