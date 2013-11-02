{-# LANGUAGE PatternGuards #-}
module Data.Integer.Presburger.Omega
  ( State
  , initState
  , checkSat
  , assert
  , Prop(..)
  , Expr(..)
  ) where

import Data.Integer.Presburger.Term
import           Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.List(partition)
import Data.Maybe(maybeToList,fromMaybe)
import Control.Applicative
import Control.Monad

infixr 2 :||
infixr 3 :&&
infix  4 :==, :/=, :<, :<=, :>, :>=
infixl 6 :+, :-
infixl 7 :*


example = test (If (x :> y) y z :== z :+ K 1)
  where
  test p = checkSat $ assert p initState
  x : y : z : _ = map Var [ 1 .. ]

--------------------------------------------------------------------------------
-- Solver interface

newtype State = State (Answer RW)

initState :: State
initState = State $ return initRW

checkSat :: State -> Maybe [(Name,Integer)]
checkSat (State m) = go m
  where
  go None            = Nothing
  go (One rw)        = Just $ filter ((>= 0) . fst) $ iModel $ inerts rw
  go (Choice m1 m2)  = mplus (go m1) (go m2)

assert :: Prop -> State -> State
assert p s = run s (prop p)




data Prop = PTrue
          | PFalse
          | Prop :|| Prop
          | Prop :&& Prop
          | Not Prop
          | Expr :== Expr
          | Expr :/= Expr
          | Expr :<  Expr
          | Expr :>  Expr
          | Expr :<= Expr
          | Expr :>= Expr

-- | Variable names must be positive
data Expr = Expr :+ Expr
          | Expr :- Expr
          | Integer :* Expr
          | Negate Expr
          | Var Int
          | K Integer
          | If Prop Expr Expr
          | Div Expr Integer
          | Mod Expr Integer

prop :: Prop -> S ()
prop PTrue       = return ()
prop PFalse      = mzero
prop (p1 :|| p2) = prop p1 `mplus` prop p2
prop (p1 :&& p2) = prop p1 >> prop p2
prop (Not p)     = prop (neg p)
  where
  neg PTrue       = PFalse
  neg PFalse      = PTrue
  neg (p1 :&& p2) = neg p1 :|| neg p2
  neg (p1 :|| p2) = neg p1 :&& neg p2
  neg (Not q)     = q
  neg (e1 :== e2) = e1 :/= e2
  neg (e1 :/= e2) = e1 :== e2
  neg (e1 :<  e2) = e1 :>= e2
  neg (e1 :<= e2) = e1 :>  e2
  neg (e1 :>  e2) = e1 :<= e2
  neg (e1 :>= e2) = e1 :<  e2

prop (e1 :== e2) = do t1 <- expr e1
                      t2 <- expr e2
                      assertEq t1 t2

prop (e1 :/= e2)  = do t1 <- expr e1
                       t2 <- expr e2
                       assertLt t1 t2 `mplus` assertLt t2 t1

prop (e1 :< e2)   = do t1 <- expr e1
                       t2 <- expr e2
                       assertLt t1 t2

prop (e1 :<= e2)  = do t1 <- expr e1
                       t2 <- expr e2
                       assertEq t1 t2 `mplus` assertLt t1 t2

prop (e1 :> e2)   = prop (e2 :<  e1)
prop (e1 :>= e2)  = prop (e2 :<= e1)


expr :: Expr -> S Term
expr (e1 :+ e2)   = (+)     <$> expr e1 <*> expr e2
expr (e1 :- e2)   = (-)     <$> expr e1 <*> expr e2
expr (k  :* e2)   = (k |*|) <$> expr e2
expr (Negate e)   = negate <$> expr e
expr (Var x)      = pure (tVar x)
expr (K x)        = pure (fromInteger x)
expr (If p e1 e2) = do x <- newVar
                       prop (p :&& Var x :== e1 :|| Not p :&& Var x :== e2)
                       return (tVar x)
expr (Div e k)    = do guard (k /= 0) -- Always Unsat
                       q <- newVar
                       prop (k :* Var q :== e)
                       return (tVar q)
expr (Mod e k)    = do guard (k /= 0) -- Always unsat
                       q <- newVar
                       r <- newVar
                       let er = Var r
                       prop (k :* Var q :+ er :== e
                                :&& er :< K k :&& K 0 :<= er)
                       return (tVar r)


assertEq :: Term -> Term -> S ()
assertEq t1 t2 =
  do i <- get inerts
     addWork qZeroTerms $ iApSubst i (t1 - t2)
     solveAll

assertLt :: Term -> Term -> S ()
assertLt t1 t2 =
  do i <- get inerts
     addWork qNegTerms $ iApSubst i (t1 - t2)
     solveAll

run :: State -> S () -> State
run (State rws) (S m) =
  State $
  do rw <- rws
     (_,rw1) <- m rw
     return rw1



--------------------------------------------------------------------------------

data RW = RW { nameSource :: !Int
             , todo       :: WorkQ
             , inerts     :: Inerts
             } deriving Show

initRW :: RW
initRW = RW { nameSource = -1, todo = qEmpty, inerts = iNone }

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
-- Constraints and Bound on Variables

ctLt :: Term -> Term -> Term
ctLt t1 t2 = t1 - t2

data Bound      = Bound Integer Term
                  deriving Show

data BoundType  = Lower | Upper
                  deriving Show

toCt :: BoundType -> Name -> Bound -> Term
toCt Lower x (Bound c t) = ctLt t              (c |*| tVar x)
toCt Upper x (Bound c t) = ctLt (c |*| tVar x) t



--------------------------------------------------------------------------------
-- Inert set

-- | The inert contains the solver state on one possible path.
data Inerts = Inerts
  { bounds :: IntMap ([Bound],[Bound])
    -- ^ Known lower and upper bounds for variables.
    -- Each bound @(c,t)@ in the first list asserts that  @t < c * x@
    -- Each bound @(c,t)@ in the second list asserts that @c * x < t@

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

        -- First, we eliminate all entries for `x`
    let (mb, mp1) = Map.updateLookupWithKey (\_ _ -> Nothing) x (bounds i)

        -- Next, we elminate all constraints that mentiond `x` in bounds
        mp2 = Map.mapWithKey extractBounds mp1

    in ( [ ct | (lbs,ubs) <- maybeToList mb
              ,  ct <- map (toCt Lower x) lbs ++ map (toCt Upper x) ubs ]
         ++
         [ ct | (_,cts) <- Map.elems mp2, ct <- cts ]

       , fmap fst mp2
       )

  extractBounds y (lbs,ubs) =
    let (lbsStay, lbsKick) = partition stay lbs
        (ubsStay, ubsKick) = partition stay ubs
    in ( (lbsStay,ubsStay)
       , map (toCt Lower y) lbsKick ++
         map (toCt Upper y) ubsKick
       )

  stay (Bound _ bnd) = not (tHasVar x bnd)


-- Given a list of lower (resp. upper) bounds, compute the least (resp. largest)
-- value that satisfies them all.
iPickBounded :: BoundType -> [Bound] -> Maybe Integer
iPickBounded bt bs = go bs Nothing
  where
  go [] mb = mb
  go (Bound c t : more) mb =
    do k <- isConst t
       let t1 = maybe k (combine k) mb
       go more $ Just $ compute t1 c

  combine = case bt of
              Lower -> max
              Upper -> min

  compute v c = case bt of
                  Lower -> div v c + 1
                  Upper -> let (q,r) = divMod v c
                           in if r == 0 then q - 1 else q


iModel :: Inerts -> [(Name,Integer)]
iModel i = goBounds [] (bounds i)
  where
  goBounds su mp =
    case Map.maxViewWithKey mp of
      Nothing -> goEqs su $ Map.toList $ solved i
      Just ((x,(lbs0,ubs0)), mp1) ->
        let lbs = [ Bound c (tLetNums su t) | Bound c t <- lbs0 ]
            ubs = [ Bound c (tLetNums su t) | Bound c t <- ubs0 ]
            sln = fromMaybe 0
                $ mplus (iPickBounded Lower lbs) (iPickBounded Upper ubs)
        in goBounds ((x,sln) : su) mp1

  goEqs su [] = su
  goEqs su ((x,t) : more) =
    let t1  = tLetNums su t
        vs  = tVarList t1
        su1 = [ (v,0) | v <- vs ] ++ (x,tConstPart t1) : su
    in goEqs su1 more


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
               then do ubs <- getBounds Upper x
                       let b    = negate xc
                           beta = s
                       addBound Lower x (Bound b beta)
                       return [ (a,alpha,b,beta) | Bound a alpha <- ubs ]
               -- XC*x + S < 0
               -- XC*x < -S
               else do lbs <- getBounds Lower x
                       let a     = xc
                           alpha = negate s
                       addBound Upper x (Bound a alpha)
                       return [ (a,alpha,b,beta) | Bound b beta <- lbs ]

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

-- | Get lower ('fst'), or upper ('snd') bounds for a variable.
getBounds :: BoundType -> Name -> S [Bound]
getBounds f x = get $ \rw -> case Map.lookup x $ bounds $ inerts rw of
                               Nothing -> []
                               Just bs -> case f of
                                            Lower -> fst bs
                                            Upper -> snd bs

addBound :: BoundType -> Name -> Bound -> S ()
addBound bt x b = updS_ $ \rw ->
  let i = inerts rw
      entry = case bt of
                Lower -> ([b],[])
                Upper -> ([],[b])
      jn (newL,newU) (oldL,oldU) = (newL++oldL, newU++oldU)
  in rw { inerts = i { bounds = Map.insertWith jn x entry (bounds i) }}

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


