{-# LANGUAGE Trustworthy, PatternGuards, BangPatterns #-}
{-|
This module implements a decision procedure for quantifier-free linear
arithmetic.  The algorithm is based on the following paper:

  An Online Proof-Producing Decision Procedure for
  Mixed-Integer Linear Arithmetic
  by
  Sergey Berezin, Vijay Ganesh, and David L. Dill
-}
module Data.Integer.SAT
  ( PropSet
  , noProps
  , checkSat
  , assert
  , Prop(..)
  , Expr(..)
  , BoundType(..)
  , getExprBound
  , getExprRange
  , Name
  , toName
  , fromName
  -- * Iterators
  , allSolutions
  , slnCurrent
  , slnNextVal
  , slnNextVar
  , slnEnumerate


  -- * Debug
  , dotPropSet
  , sizePropSet
  , allInerts
  , ppInerts
  ) where

import Debug.Trace

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.List(partition)
import           Data.Maybe(maybeToList,fromMaybe,mapMaybe)
import           Control.Applicative(Applicative(..), (<$>))
import           Control.Monad(liftM,ap,MonadPlus(..),guard)
import           Text.PrettyPrint

infixr 2 :||
infixr 3 :&&
infix  4 :==, :/=, :<, :<=, :>, :>=
infixl 6 :+, :-
infixl 7 :*

--------------------------------------------------------------------------------
-- Solver interface

-- | A collection of propositions.
newtype PropSet = State (Answer RW)
                  deriving Show

dotPropSet :: PropSet -> Doc
dotPropSet (State a) = dotAnswer (ppInerts . inerts) a

sizePropSet :: PropSet -> (Integer,Integer,Integer)
sizePropSet (State a) = answerSize a

-- | An empty collection of propositions.
noProps :: PropSet
noProps = State $ return initRW

-- | Add a new proposition to an existing collection.
assert :: Prop -> PropSet -> PropSet
assert p (State rws) = State $ fmap snd $ m =<< rws
  where S m = prop p

-- | Extract a model from a consistent set of propositions.
-- Returns 'Nothing' if the assertions have no model.
-- If a variable does not appear in the assignment, then it is 0 (?).
checkSat :: PropSet -> Maybe [(Int,Integer)]
checkSat (State m) = go m
  where
  go None            = mzero
  go (One rw)        = return [ (x,v) | (UserName x, v) <- iModel (inerts rw) ]
  go (Choice m1 m2)  = mplus (go m1) (go m2)

allInerts :: PropSet -> [Inerts]
allInerts (State m) = map inerts (toList m)

allSolutions :: PropSet -> [Solutions]
allSolutions = map startIter . allInerts


-- | Computes bounds on the expression that are compatible with the model.
-- Returns `Nothing` if the bound is not known.
getExprBound :: BoundType -> Expr -> PropSet -> Maybe Integer
getExprBound bt e (State s) =
  do let S m          = expr e
         check (t,s1) = iTermBound bt t (inerts s1)
     bs <- mapM check $ toList $ s >>= m
     case bs of
       [] -> Nothing
       _  -> Just (maximum bs)

-- | Compute the range of possible values for an expression.
-- Returns `Nothing` if the bound is not known.
getExprRange :: Expr -> PropSet -> Maybe [Integer]
getExprRange e (State s) =
  do let S m          = expr e
         check (t,s1) = do l <- iTermBound Lower t (inerts s1)
                           u <- iTermBound Upper t (inerts s1)
                           return (l,u)
     bs <- mapM check $ toList $ s >>= m
     case bs of
       [] -> Nothing
       _  -> let (ls,us) = unzip bs
             in Just [ x | x <- [ minimum ls .. maximum us ] ]



-- | The type of proposition.
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
            deriving (Read,Show)

-- | The type of integer expressions.
-- Variable names must be non-negative.
data Expr = Expr :+ Expr          -- ^ Addition
          | Expr :- Expr          -- ^ Subtraction
          | Integer :* Expr       -- ^ Multiplication by a constant
          | Negate Expr           -- ^ Negation
          | Var Name              -- ^ Variable
          | K Integer             -- ^ Constant
          | If Prop Expr Expr     -- ^ A conditional expression
          | Div Expr Integer      -- ^ Division, rounds down
          | Mod Expr Integer      -- ^ Non-negative remainder
            deriving (Read,Show)

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
                      solveIs0 (t1 |-| t2)

prop (e1 :/= e2)  = do t1 <- expr e1
                       t2 <- expr e2
                       let t = t1 |-| t2
                       solveIsNeg t `orElse` solveIsNeg (tNeg t)

prop (e1 :< e2)   = do t1 <- expr e1
                       t2 <- expr e2
                       solveIsNeg (t1 |-| t2)

prop (e1 :<= e2)  = do t1 <- expr e1
                       t2 <- expr e2
                       let t = t1 |-| t2
                       solveIs0 t `orElse` solveIsNeg t

prop (e1 :> e2)   = prop (e2 :<  e1)
prop (e1 :>= e2)  = prop (e2 :<= e1)


expr :: Expr -> S Term
expr (e1 :+ e2)   = (|+|)   <$> expr e1 <*> expr e2
expr (e1 :- e2)   = (|-|)   <$> expr e1 <*> expr e2
expr (k  :* e2)   = (k |*|) <$> expr e2
expr (Negate e)   = tNeg    <$> expr e
expr (Var x)      = pure (tVar x)
expr (K x)        = pure (tConst x)
expr (If p e1 e2) = do x <- newVar
                       prop (p :&& Var x :== e1 :|| Not p :&& Var x :== e2)
                       return (tVar x)
expr (Div e k)    = fmap fst $ exprDivMod e k
expr (Mod e k)    = fmap snd $ exprDivMod e k

exprDivMod :: Expr -> Integer -> S (Term,Term)
exprDivMod e k =
  do guard (k /= 0) -- Always unsat
     q <- newVar
     r <- newVar
     let er = Var r
     prop (k :* Var q :+ er :== e :&& er :< K k :&& K 0 :<= er)
     return (tVar q, tVar r)





--------------------------------------------------------------------------------

data RW = RW { nameSource :: !Int
             , inerts     :: Inerts
             } deriving Show

initRW :: RW
initRW = RW { nameSource = 0, inerts = iNone }

--------------------------------------------------------------------------------
-- Constraints and Bound on Variables

ctLt :: Term -> Term -> Term
ctLt t1 t2 = t1 |-| t2

ctEq :: Term -> Term -> Term
ctEq t1 t2 = t1 |-| t2

data Bound      = Bound Integer Term  -- ^ The integer is strictly positive
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
  { bounds :: NameMap ([Bound],[Bound])
    -- ^ Known lower and upper bounds for variables.
    -- Each bound @(c,t)@ in the first list asserts that  @t < c * x@
    -- Each bound @(c,t)@ in the second list asserts that @c * x < t@

  , solved :: NameMap Term
    -- ^ Definitions for resolved variables.
    -- These form an idempotent substitution.
  } deriving Show

ppInerts :: Inerts -> Doc
ppInerts is = vcat $ [ ppLower x b | (x,(ls,_)) <- bnds, b <- ls ] ++
                     [ ppUpper x b | (x,(_,us)) <- bnds, b <- us ] ++
                     [ ppEq e      | e <- Map.toList (solved is) ]
  where
  bnds = Map.toList (bounds is)

  ppT c x                = ppTerm (c |*| tVar x)
  ppLower x (Bound c t)  = ppTerm t <+> text "<" <+> ppT c x
  ppUpper x (Bound c t)  = ppT c x  <+> text "<" <+> ppTerm t
  ppEq (x,t)             = ppName x <+> text "=" <+> ppTerm t



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
--    * The kicked-out constraints are NOT rewritten, this happens
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


-- | Given some lower and upper bounds, find the interval the satisfies them.
-- Note the upper and lower bounds are strict (i.e., < and >)
boundInterval :: [Bound] -> [Bound] -> Maybe (Maybe Integer, Maybe Integer)
boundInterval lbs ubs =
  do ls <- mapM (normBound Lower) lbs
     us <- mapM (normBound Upper) ubs
     let lb = case ls of
                [] -> Nothing
                _  -> Just (maximum ls + 1)
         ub = case us of
                [] -> Nothing
                _  -> Just (minimum us - 1)
     case (lb,ub) of
       (Just l, Just u) -> guard (l <= u)
       _                -> return ()
     return (lb,ub)
  where
  normBound Lower (Bound c t) = do k <- isConst t
                                   return (div (k + c - 1) c)
  normBound Upper (Bound c t) = do k <- isConst t
                                   return (div k c)

data Solutions = Done
               | TopVar Name Integer (Maybe Integer) (Maybe Integer) Inerts
               | FixedVar Name Integer Solutions
                  deriving Show

slnCurrent :: Solutions -> [(Int,Integer)]
slnCurrent s = [ (x,v) | (UserName x, v) <- go s ]
  where
  go Done                = []
  go (TopVar x v _ _ is) = (x, v) : iModel (iLet x v is)
  go (FixedVar x v i)    = (x, v) : go i

-- | Replace occurances of a variable with an integer.
-- WARNING: The integer should be a valid value for the variable.
iLet :: Name -> Integer -> Inerts -> Inerts
iLet x v is = Inerts { bounds = fmap updBs (bounds is)
                     , solved = fmap (tLetNum x v) (solved is) }
  where
  updB (Bound c t) = Bound c (tLetNum x v t)
  updBs (ls,us)    = (map updB ls, map updB us)


startIter :: Inerts -> Solutions
startIter is =
  case Map.maxViewWithKey (bounds is) of
    Nothing ->
      case Map.maxViewWithKey (solved is) of
        Nothing -> Done
        Just ((x,t), mp1) ->
          case [ y | y <- tVarList t ] of
            y : _ -> TopVar y 0 Nothing Nothing is
            [] -> let v = tConstPart t
                  in TopVar x v (Just v) (Just v) $ is { solved = mp1 }
    Just ((x,(lbs,ubs)), mp1) ->
      case [ y | Bound _ t <- lbs ++ ubs, y <- tVarList t ] of
        y : _ -> TopVar y 0 Nothing Nothing is
        [] -> case boundInterval lbs ubs of
                Nothing -> error "bug: cannot compute interval?"
                Just (lb,ub) ->
                  let v = fromMaybe 0 (mplus lb ub)
                  in TopVar x v lb ub $ is { bounds = mp1 }

slnEnumerate :: Solutions -> [ Solutions ]
slnEnumerate s0 = go s0 []
  where
  go s k  = case slnNextVar s of
              Nothing -> hor s k
              Just s1 -> go s1 $ case slnNextVal s of
                                   Nothing -> k
                                   Just s2 -> go s2 k

  hor s k = s
          : case slnNextVal s of
              Nothing -> k
              Just s1 -> hor s1 k

slnNextVal :: Solutions -> Maybe Solutions
slnNextVal Done = Nothing
slnNextVal (FixedVar x v i) = FixedVar x v `fmap` slnNextVal i
slnNextVal it@(TopVar _ _ lb _ _) =
  case lb of
    Just _  -> slnNextValWith (+1) it
    Nothing -> slnNextValWith (subtract 1) it


slnNextValWith :: (Integer -> Integer) -> Solutions -> Maybe Solutions
slnNextValWith _ Done = Nothing
slnNextValWith f (FixedVar x v i) = FixedVar x v `fmap` slnNextValWith f i
slnNextValWith f (TopVar x v lb ub is) =
  do let v1 = f v
     case lb of
       Just l  -> guard (l <= v1)
       Nothing -> return ()
     case ub of
       Just u  -> guard (v1 <= u)
       Nothing -> return ()
     return $ TopVar x v1 lb ub is

slnNextVar :: Solutions -> Maybe Solutions
slnNextVar Done = Nothing
slnNextVar (TopVar x v _ _ is) = Just $ FixedVar x v $ startIter $ iLet x v is
slnNextVar (FixedVar x v i)    = FixedVar x v `fmap` slnNextVar i




-- Given a list of lower (resp. upper) bounds, compute the least (resp. largest)
-- value that satisfies them all.
iPickBounded :: BoundType -> [Bound] -> Maybe Integer
iPickBounded _ [] = Nothing
iPickBounded bt bs =
  do xs <- mapM (normBound bt) bs
     return $ case bt of
                Lower -> maximum xs
                Upper -> minimum xs
  where
  -- t < c*x
  -- <=> t+1 <= c*x
  -- <=> (t+1)/c <= x
  -- <=> ceil((t+1)/c) <= x
  -- <=> t `div` c + 1 <= x
  normBound Lower (Bound c t) = do k <- isConst t
                                   return (k `div` c + 1)
  -- c*x < t
  -- <=> c*x <= t-1
  -- <=> x   <= (t-1)/c
  -- <=> x   <= floor((t-1)/c)
  -- <=> x   <= (t-1) `div` c
  normBound Upper (Bound c t) = do k <- isConst t
                                   return (div (k-1) c)


-- | The largest (resp. least) upper (resp. lower) bound on a term
-- that will satisfy the model
iTermBound :: BoundType -> Term -> Inerts -> Maybe Integer
iTermBound bt (T k xs) is = do ks <- mapM summand (Map.toList xs)
                               return $ sum $ k : ks
  where
  summand (x,c) = fmap (c *) (iVarBound (newBt c) x is)
  newBt c = if c > 0 then bt else case bt of
                                    Lower -> Upper
                                    Upper -> Lower


-- | The largest (resp. least) upper (resp. lower) bound on a variable
-- that will satisfy the model.
iVarBound :: BoundType -> Name -> Inerts -> Maybe Integer
iVarBound bt x is
  | Just t <- Map.lookup x (solved is) = iTermBound bt t is

iVarBound bt x is =
  do both <- Map.lookup x (bounds is)
     case mapMaybe fromBound (chooseBounds both) of
       [] -> Nothing
       bs -> return (combineBounds bs)
  where
  fromBound (Bound c t) = fmap (scaleBound c) (iTermBound bt t is)

  combineBounds = case bt of
                    Upper -> minimum
                    Lower -> maximum

  chooseBounds = case bt of
                   Upper -> snd
                   Lower -> fst

  scaleBound c b = case bt of
                     Upper -> div (b-1) c
                     Lower -> div b c + 1




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

solveIs0 :: Term -> S ()
solveIs0 t = solveIs0' =<< apSubst t

-- | Solve a constraint if the form @t = 0@.
-- Assumes substitution has already been applied.
solveIs0' :: Term -> S ()
solveIs0' t

  -- A == 0
  | Just a <- isConst t = guard (a == 0)

  -- A + B * x = 0
  | Just (a,b,x) <- tIsOneVar t =
    case divMod (-a) b of
      (q,0) -> addDef x (tConst q)
      _     -> mzero

  --  x + S = 0
  -- -x + S = 0
  | Just (xc,x,s) <- tGetSimpleCoeff t =
    addDef x (if xc > 0 then tNeg s else s)

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
         addDef xk soln

         let upd i = div (2*i + m) (2*m) + modulus i m
         solveIs0 (negate (abs ak) |*| tVar v |+| tMapCoeff upd s)

  | otherwise = error "solveIs0: unreachable"

modulus :: Integer -> Integer -> Integer
modulus a m = a - m * div (2 * a + m) (2 * m)


solveIsNeg :: Term -> S ()
solveIsNeg t = solveIsNeg' =<< apSubst t


-- | Solve a constraint of the form @t < 0@.
-- Assumes that substitution has been applied
solveIsNeg' :: Term -> S ()
solveIsNeg' t

  -- A < 0
  | Just a <- isConst t = guard (a < 0)

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

orElse :: S () -> S () -> S ()
orElse x y = mplus x y

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


answerSize :: Answer a -> (Integer,Integer,Integer)
answerSize = go 0 0 0
  where
  go !n !o !c ans =
    case ans of
      None  -> (n+1, o, c)
      One _ -> (n, o + 1, c)
      Choice x y ->
        case go n o (c+1) x of
          (n',o',c') -> go n' o' c' y


dotAnswer :: (a -> Doc) -> Answer a -> Doc
dotAnswer pp g0 = vcat [text "digraph {", nest 2 (fst $ go 0 g0), text "}"]
  where
  node x d            = integer x <+> brackets (text "label=" <> text (show d))
                                                              <> semi
  edge x y            = integer x <+> text "->" <+> integer y

  go x None           = let x' = x + 1
                        in seq x' ( node x "", x' )
  go x (One a)        = let x' = x + 1
                        in seq x' ( node x (show (pp a)), x' )
  go x (Choice c1 c2) = let x'       = x + 1
                            (ls1,x1) = go x' c1
                            (ls2,x2) = go x1    c2
                        in seq x'
                           ( vcat [ node x "|"
                                  , edge x x'
                                  , edge x x1
                                  , ls1
                                  , ls2
                                  ], x2 )
toList :: Answer a -> [a]
toList a = go a []
  where
  go (Choice xs ys) zs = go xs (go ys zs)
  go (One x) xs        = x : xs
  go None xs           = xs


instance Monad Answer where
  return a           = One a
  fail _             = None
  None >>= _         = None
  One a >>= k        = k a
  Choice m1 m2 >>= k = mplus (m1 >>= k) (m2 >>= k)

instance MonadPlus Answer where
  mzero                = None
  mplus None x         = x
  -- mplus (Choice x y) z = mplus x (mplus y z)
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
newVar = updS $ \rw -> ( SysName (nameSource rw)
                       , rw { nameSource = nameSource rw + 1 }
                       )

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
addDef x t =
  do newWork <- updS $ \rw -> let (newWork,newInerts) = iSolved x t (inerts rw)
                              in (newWork, rw { inerts = newInerts })
     mapM_ solveIsNeg newWork

apSubst :: Term -> S Term
apSubst t =
  do i <- get inerts
     return (iApSubst i t)




--------------------------------------------------------------------------------


data Name = UserName !Int | SysName !Int
            deriving (Read,Show,Eq,Ord)

ppName :: Name -> Doc
ppName (UserName x) = text "u" <> int x
ppName (SysName x)  = text "s" <> int x

toName :: Int -> Name
toName = UserName

fromName :: Name -> Maybe Int
fromName (UserName x) = Just x
fromName (SysName _)  = Nothing




type NameMap = Map Name

-- | The type of terms.  The integer is the constant part of the term,
-- and the `Map` maps variables (represented by @Int@ to their coefficients).
-- The term is a sum of its parts.
-- INVARIANT: the `Map` does not map anything to 0.
data Term = T !Integer (NameMap Integer)
              deriving (Eq,Ord)

infixl 6 |+|, |-|
infixr 7 |*|

-- | A constant term.
tConst :: Integer -> Term
tConst k = T k Map.empty

-- | Construct a term with a single variable.
tVar :: Name -> Term
tVar x = T 0 (Map.singleton x 1)

(|+|) :: Term -> Term -> Term
T n1 m1 |+| T n2 m2 = T (n1 + n2)
                    $ if Map.null m1 then m2 else
                      if Map.null m2 then m1 else
                      Map.filter (/= 0) $ Map.unionWith (+) m1 m2

(|*|) :: Integer -> Term -> Term
0 |*| _     = tConst 0
1 |*| t     = t
k |*| T n m = T (k * n) (fmap (k *) m)

tNeg :: Term -> Term
tNeg t = (-1) |*| t

(|-|) :: Term -> Term -> Term
t1 |-| t2 = t1 |+| tNeg t2


-- | Replace a variable with a term.
tLet :: Name -> Term -> Term -> Term
tLet x t1 t2 = let (a,t) = tSplitVar x t2
               in a |*| t1 |+| t

-- | Replace a variable with a constant.
tLetNum :: Name -> Integer -> Term -> Term
tLetNum x k t = let (c,T n m) = tSplitVar x t
                in T (c * k + n) m

-- | Replace the given variables with constants.
tLetNums :: [(Name,Integer)] -> Term -> Term
tLetNums xs t = foldr (\(x,i) t1 -> tLetNum x i t1) t xs




instance Show Term where
  showsPrec c t = showsPrec c (show (ppTerm t))

ppTerm :: Term -> Doc
ppTerm (T k m) =
  case Map.toList m of
    [] -> integer k
    xs | k /= 0 -> hsep (integer k : map ppProd xs)
    x : xs      -> hsep (ppFst x   : map ppProd xs)

  where
  ppFst (x,1)   = ppName x
  ppFst (x,-1)  = text "-" <> ppName x
  ppFst (x,n)   = ppMul n x

  ppProd (x,1)  = text "+" <+> ppName x
  ppProd (x,-1) = text "-" <+> ppName x
  ppProd (x,n) | n > 0      = text "+" <+> ppMul n x
               | otherwise  = text "-" <+> ppMul (abs n) x

  ppMul n x = integer n <+> text "*" <+> ppName x

-- | Remove a variable from the term, and return its coefficient.
-- If the variable is not present in the term, the coefficient is 0.
tSplitVar :: Name -> Term -> (Integer, Term)
tSplitVar x t@(T n m) =
  case Map.updateLookupWithKey (\_ _ -> Nothing) x m of
    (Nothing,_) -> (0,t)
    (Just k,m1) -> (k, T n m1)

-- | Does the term contain this varibale?
tHasVar :: Name -> Term -> Bool
tHasVar x (T _ m) = Map.member x m

-- | Is this terms just an integer.
isConst :: Term -> Maybe Integer
isConst (T n m)
  | Map.null m  = Just n
  | otherwise   = Nothing

tConstPart :: Term -> Integer
tConstPart (T n _) = n

-- | Returns: @Just (a, b, x)@ if the term is the form: @a + b * x@
tIsOneVar :: Term -> Maybe (Integer, Integer, Name)
tIsOneVar (T a m) = case Map.toList m of
                      [ (x,b) ] -> Just (a, b, x)
                      _         -> Nothing

-- | Spots terms that contain variables with unit coefficients
-- (i.e., of the form @x + t@ or @t - x@).
-- Returns (coeff, var, rest of term)
tGetSimpleCoeff :: Term -> Maybe (Integer, Name, Term)
tGetSimpleCoeff (T a m) =
  do let (m1,m2) = Map.partition (\x -> x == 1 || x == -1) m
     ((x,xc), m3) <- Map.minViewWithKey m1
     return (xc, x, T a (Map.union m3 m2))

tVarList :: Term -> [Name]
tVarList (T _ m) = Map.keys m


-- | Try to factor-out a common consant (> 1) from a term.
-- For example, @2 + 4x@ becomes @2 * (1 + 2x)@.
tFactor :: Term -> Maybe (Integer, Term)
tFactor (T c m) =
  do d <- common (c : Map.elems m)
     return (d, T (div c d) (fmap (`div` d) m))
  where
  common :: [Integer] -> Maybe Integer
  common []  = Nothing
  common [x] = Just x
  common (x : y : zs) =
    case gcd x y of
      1 -> Nothing
      n -> common (n : zs)

-- | Extract a variable with a coefficient whose absolute value is minimal.
tLeastAbsCoeff :: Term -> Maybe (Integer, Name, Term)
tLeastAbsCoeff (T c m) = do (xc,x,m1) <- Map.foldWithKey step Nothing m
                            return (xc, x, T c m1)
  where
  step x xc Nothing   = Just (xc, x, Map.delete x m)
  step x xc (Just (yc,_,_))
    | abs xc < abs yc = Just (xc, x, Map.delete x m)
  step _ _ it         = it

-- | Extract the least variable from a term
tLeastVar :: Term -> Maybe (Integer, Name, Term)
tLeastVar (T c m) =
  do ((x,xc), m1) <- Map.minViewWithKey m
     return (xc, x, T c m1)

-- | Apply a function to all coefficients, including the constnat
tMapCoeff :: (Integer -> Integer) -> Term -> Term
tMapCoeff f (T c m) = T (f c) (fmap f m)







