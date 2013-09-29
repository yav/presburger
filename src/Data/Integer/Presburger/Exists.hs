{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Data.Integer.Presburger.Exists(exists) where

import Data.Integer.Presburger.Term
import Data.Integer.Presburger.Formula

{-| A type used while eliminating the quantifier for a variable.
The atoms are normalized so that the variable is on its own and has
coefficient 1. -}
data CtFo     = Fo Formula              -- ^ The varibale does not appear here
              | CtConnF !Conn CtFo CtFo -- ^ Connective
              | CtAtomF Ct              -- ^ Normalized atom

{-| Note that it is important that the 'Integer' in 'DivCt' is lazy,
so that we generate the constraint in a single pass. -}
data Ct       = AtomCt Pol PredS   Name Term    -- ^ @x `op` t@
              | DivCt  Pol Integer Name Term    -- ^ @k | (x + t)@

{- | Construct formulas so that parts that do not mention the quantified
variabele float to the front. -}
ctConn :: Conn -> CtFo -> CtFo -> CtFo
ctConn c (Fo lf) (CtConnF c' (Fo rf) rest)
  | c == c'           = CtConnF c (Fo (fConn c lf rf)) rest

-- Quantifiers commute
ctConn c (CtConnF c' (Fo lf) rest) (Fo rf)
  | c == c'           = CtConnF c (Fo (fConn c lf rf)) rest

ctConn c (CtConnF c' (Fo lf) rest) (CtConnF c'' (Fo rf) rest')
  | c == c' && c == c'' = CtConnF c (Fo (fConn c lf rf))
                                    (CtConnF c rest rest')

ctConn c lf rf@(Fo _) = CtConnF c rf lf

ctConn c lf rf        = CtConnF c lf rf




-- | Collect all constraints in a constraint-formula.
getCts :: CtFo -> [Ct] -> [Ct]
getCts ctfo more =
  case ctfo of
    Fo _            -> more
    CtConnF _ f1 f2 -> getCts f1 (getCts f2 more)
    CtAtomF ct      -> ct : more

-- | Convert a constraint-formula back into a normal formula.
ctAtoms :: (Ct -> Atom) -> CtFo -> Formula
ctAtoms f ctfo =
  case ctfo of
    Fo fo           -> fo
    CtConnF c f1 f2 -> fConn c (ctAtoms f f1) (ctAtoms f f2)
    CtAtomF ct      -> fAtom (f ct)




{- | Transform an atom so that the variable is on the LHS with coefficient 1.
If the variable is not mentioned in the atom, then it is left unchanged,
and we return 'Nothing'. Otherwise, we update the LCMs of coeffieicnts
and compute a normalized constraint. -}

-- 5 * x = 10
-- x = 2

aCt :: Name    ->   -- ^ Variable.
       Integer ->   -- ^ LCM of all coefficients for the variable (LAZY).
       Integer ->   -- ^ Partial LCM of coefficients.
       Atom    ->   -- ^ Constraint to be normalizied.
       Maybe (Integer, Ct)
       -- ^ (Updated LCM of coefficients, constraint)

-- Does it occur on the left?
aCt x lcmCoeffFinal lcmCoeff (isAtom -> Just (pol,op,lhs,rhs))
  | k /= 0 = Just ( lcm k lcmCoeff
                  , AtomCt pol op x (div lcmCoeffFinal k |*| (rhs - lRest))
                  )
  where
  (k, lRest) = tSplitVar x lhs

-- Does it occur on the right?
aCt x lcmCoeffFinal lcmCoeff (isAtom -> Just (pol,op,lhs,rhs))
  | k /= 0 = Just ( lcm k lcmCoeff
                  , AtomCt newP newOp x (div lcmCoeffFinal k |*| (lhs - rRest))
                  )
  where
  (k, rRest)   = tSplitVar x rhs

  -- Because we are moving the variable to the LHS, we need to update
  -- the operations.
  (newP,newOp) = case pol of
                   Pos ->
                     case op of
                       Eq  -> (Pos,Eq)    -- same
                       Lt  -> (Neg,Leq)   -- <  becomes >
                       Leq -> (Neg,Lt)    -- <= becomes >=
                   Neg ->
                     case op of
                       Eq  -> (Neg,Eq)    -- same
                       Lt  -> (Pos,Leq)   -- >= becomes <=
                       Leq -> (Pos,Lt)    -- >  becomes <

-- Does it occur in a divisibility constraint?
-- m | (k * x + t) <=> abs (sc * m) | (sc * k * x + sc * t)
-- where sc * k = lcmCoeffFinal
aCt x lcmCoeffFinal lcmCoeff (isDiv -> Just (p,m,t))
  | k /= 0  = let sc = div lcmCoeffFinal k
                  m1 = abs (m * sc)
              in Just ( lcm lcmCoeff k
                      , DivCt p m1 x (sc |*| rest)
                      )
  where (k,rest) = tSplitVar x t

-- It does not occur anywhere.
aCt _ _ _ _ = Nothing


{-| Normalize a formula with respect to a particular variable.
In the resulting formula, the variable (technically, a new variable with
the same name) has coefficient 1.
Example: @2x > 5 --> x > 10@

As a result we return:
    * the LCM of all coefficients of the variables,
    * Parts of the formula that do not mention the variable are
      tagged with 'Fo'.
-}
aCts :: Name -> Formula -> (Integer, CtFo)
aCts x form = ( lcmCoeffFinal
              , ctConn And foFinal (CtAtomF $ DivCt Pos lcmCoeffFinal x 0)
              )
  where
  (lcmCoeffFinal,foFinal) = go True 1 form

  go _ lcmCoeff f
    | Just a <- isFAtom f =
    case aCt x lcmCoeffFinal lcmCoeff a of -- RECURSION: cf lcmCoeffFinal
      Just (lcmCoeff', ct) -> (lcmCoeff', CtAtomF ct)
      Nothing              -> (lcmCoeff,  Fo f)

  go _ lcmCoeff f
    | ~(Just (c,l,r)) <- isFConn f =
    case go (c == Or) lcmCoeff l of
      (lcmCoeff1, l') ->
         case go (c == Or) lcmCoeff1 r of
           (lcmCoeff2, r') ->
              case (l',r') of
                (Fo _,Fo _) -> (lcmCoeff, Fo f)
                _           -> (lcmCoeff2, ctConn c l' r')


computeDelta :: CtFo -> (Integer, CtFo)
computeDelta = go True 1
  where

  {- The boolean paramter to 'go' indicates if we should try the equality
     optimization. We implement this in `tryEqOpt` which flattens
     a conjunction and looks for equalities.  If we don't find any equalities,
     we go back to the `go` function, but now we disable the optimization,
     to avoid an infinite loop.   The optimization is autmoatically re-enabled
     when we go under a disjunction.
  -}


  go opt !lcmDiv fo =
    case fo of
      CtAtomF (DivCt _ m _ _)   -> (lcm m lcmDiv, fo)
      CtConnF And f1 f2 | opt   -> tryEqOpt lcmDiv f1 [f2] []
      CtConnF c f1 f2           -> let (lcmDiv1, f1') = go (c == Or) lcmDiv  f1
                                       (lcmDiv2, f2') = go (c == Or) lcmDiv1 f2

                                   in (lcmDiv2, ctConn c f1' f2')
      Fo _                      -> (lcmDiv, fo)
      CtAtomF _                 -> (lcmDiv, fo)

  {- The Equality Optmization

  We look for pattrens of the form:                `x = t /\ P`.
  When we spot this pattern, we can continue with: `x = t /\ P (t/x)`.

  The benfit of this is that now `P` does not mention `x`, which results
  in less work when eliminating quantifiers (e.g., `lcmDiv` will be smaller). -}

  tryEqOpt d fo@(CtAtomF (AtomCt Pos Eq _ t)) todo done =
    (d, case todo ++ done of
          []   -> fo
          more -> CtConnF And (Fo $ foldl1 (fConn And)
                                    (map (addDef t) more)) fo)

  tryEqOpt d (CtConnF And f1 f2) todo done = tryEqOpt d f1 (f2 : todo) done
  tryEqOpt d f (f1 : todo) done = tryEqOpt d f1 todo (f : done)
  tryEqOpt d f [] done          = go False d (foldl (CtConnF And) f done)

  addDef t ctfo = ctAtoms (letAtom t) ctfo

-- | Given some constraints, collect the upper/lower bound restrictions on
-- them.  We have a strategy that can use either the lower bounds or the
-- upper bounds.  However, we need to perform a check for each separate
-- bound, so we are interested in the shorter list.  This is what the sum
-- is for: 'Left': there were fewer lower bounds, 'Right': fewer upper bounds
getBounds :: [Ct] -> Either [Term] [Term]
getBounds = go (0::Int) [] []
  where
  go !d !ls !us (AtomCt pol op _ rhs : more) =
    case (pol,op) of
      (Pos,Lt ) -> go (d+1) ls             (rhs : us)     more
      (Neg,Leq) -> go (d-1) (rhs : ls)     us             more
      (Pos,Leq) -> go (d+1) ls             (rhs + 1 : us) more
      (Neg,Lt ) -> go (d-1) (rhs - 1 : ls) us             more
      (Pos,Eq ) -> go d     (rhs - 1 : ls) (rhs + 1 : us) more
      (Neg,Eq ) -> go d     (rhs : ls)     (rhs : us)     more

  go d ls us (DivCt {} : more) = go d ls us more
  go d ls us []                = if d >= 0 then Left ls else Right us


-- | Case when variable gets arbitrarily small.
fNegInfAtom :: Integer -> Ct -> Atom
fNegInfAtom _ (AtomCt pol op _ _) = mkBool $ evalPol pol $ case op of
                                                             Eq  -> False
                                                             Lt  -> True
                                                             Leq -> True
fNegInfAtom j (DivCt pol m _ t)   = mkDiv pol m (j |+| t)


-- | Case when variable gets arbitrarily large.
posInfAtom :: Integer -> Ct -> Atom
posInfAtom _ (AtomCt pol _ _ _) = mkBool $ case pol of
                                             Pos -> False -- eq,lt,leq:all False
                                             Neg -> True  -- fNegations are true
posInfAtom j (DivCt p m _ t)    = mkDiv p m (j |+| t)

-- | Replace the variable in a constraint with the given term.
letAtom :: Term -> Ct -> Atom
letAtom b (AtomCt pol op _ rhs) = mkAtom pol op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b)
letAtom b (DivCt p m _ t) = mkDiv p m (b + t)



-- XXX:
-- Optimization 2: When we are eliminating top-level quantifiers,
-- we don't need to do all of [ 1 .. delta ]

ex :: Name -> Formula -> Formula
ex x fo
  | Just (Or, f1, f2) <- isFConn fo = fConn Or (ex x f1) (ex x f2)
  | otherwise =
  case ctFo of
    Fo f -> f -- Did not mention variable, nothing to do.
    _    ->
      case getBounds (getCts ctFo []) of
        Left lowerBounds  ->
          fConns Or $
          [ ctAtoms (fNegInfAtom j) ctFo
          | j <- [ 1 .. delta ] ]
          ++
          [ ctAtoms (letAtom (j |+| b)) ctFo
          | j <- [ 1 .. delta ], b <- lowerBounds ]

        Right upperBounds ->
          fConns Or $
          [ ctAtoms (posInfAtom (negate j)) ctFo
          | j <- [ 1 .. delta ] ]
          ++
          [ ctAtoms (letAtom (negate j |+| a)) ctFo
          | j <- [ 1 .. delta ], a <- upperBounds ]
  where
  (_coeff, ctFo0) = aCts x fo
  (delta, ctFo)   = computeDelta ctFo0

exists :: [Name] -> Formula -> Formula
exists xs f = foldr ex f xs

instance Show Ct where
  showsPrec p = showsPrec p . toAtom

instance Show CtFo where
  showsPrec p = showsPrec p . ctAtoms toAtom

toAtom :: Ct -> Atom
toAtom (AtomCt p op x t) = mkAtom p op (tVar x) t
toAtom (DivCt p m x t)   = mkDiv p m (tVar x + t)


