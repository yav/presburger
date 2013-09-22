{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}
module Data.Integer.Presburger.Atom
  ( Formula (..), Conn (..), Atom (..), Pol(..), PredS(..)
  , exists
  , isTrue
  ) where

import Data.Integer.Presburger.Term
import Text.PrettyPrint
import Data.List(partition)
import Control.Monad(liftM2)

data Formula  = AtomF Atom
              | ConnF !Conn Formula Formula

data CtFo     = Fo Formula
              | CtConnF !Conn CtFo CtFo
              | CtAtomF Ct

data Conn   = And | Or
              deriving (Show, Eq)

getCts :: CtFo -> [Ct] -> [Ct]
getCts ctfo more =
  case ctfo of
    Fo _            -> more
    CtConnF _ f1 f2 -> getCts f1 (getCts f2 more)
    CtAtomF ct      -> ct : more

ctAtoms :: (Ct -> Atom) -> CtFo -> Formula
ctAtoms f ctfo =
  case ctfo of
    Fo fo           -> fo
    CtConnF c f1 f2 -> ConnF c (ctAtoms f f1) (ctAtoms f f2)
    CtAtomF ct      -> AtomF (f ct)


fLet :: Name -> Term -> Formula -> Formula
fLet x t fo =
  case fo of
    ConnF c f1 f2 -> ConnF c (fLet x t f1) (fLet x t f2)
    AtomF a ->
      case a of
        Atom p s t1 t2 ->
          let (lhs,rhs) = tSplit $ tLet x t $ t2 - t1
          in AtomF (mkAtom p s lhs rhs)
        Div  p m t1    -> AtomF (mkDiv p m (tLet x t t1))
        Bool _         -> fo

-- | Basic propositions.
data Atom   = Atom !Pol !PredS Term Term  -- ^ Comparisons
            | Div  !Pol !Integer Term     -- ^ Divisibility assertions
            | Bool !Bool                  -- ^ Constants
              deriving Eq

-- | Polarity of atoms.
data Pol    = Pos     -- ^ Normal atom.
            | Neg     -- ^ Negated atom.
              deriving Eq

-- | Binary predicate symbols.
data PredS  = Eq | Lt | Leq
              deriving Eq



mkAtom :: Pol -> PredS -> Term -> Term -> Atom
mkAtom p s t1 t2 =
  let a = Atom p s t1 t2
  in case evalAtom a of
       Just b  -> Bool b
       Nothing -> a

mkDiv :: Pol -> Integer -> Term -> Atom
mkDiv p m t =
  let a = Div p m t
  in case evalAtom a of
       Just b  -> Bool b
       Nothing -> a




{- | A type used while eliminating the quantifier for a variable.
The atoms are normalized so that the variable is on its own and has
coefficient 1.

Note that it is important that the 'Integer' in 'DivCt' is lazy,
so that we generate the constraint in a single pass. -}
data Ct     = AtomCt Pol PredS   Name Term    -- x `op` t
            | DivCt  Pol Integer Name Term  -- k | (x + t)

{- | Transform an atom so that the variable is on the LHS with coefficient 1.
If the variable is not mentioned in the atom, then it is left unchanged,
and we return 'Nothing'. Otherwise, we update the LCMs of coeffieicnts
and divisors as necessary, and compute a normalized constraint. -}

aCt :: Name    ->   -- ^ Variable.
       Integer ->   -- ^ LCM of all coefficients for the variable (LAZY).
       Integer ->   -- ^ Partial LCM of coefficients.
       Integer ->   -- ^ Partial LCM of divisors.
       Atom    ->   -- ^ Constraint to be normalizied.
       Maybe (Integer, Integer, Ct)
       -- ^ (Updated LCM of coefficients, updated LCM of divisors, constraint)

-- Does it occur on the left?
aCt x lcmCoeffFinal lcmCoeff lcmDiv (Atom pol op lhs rhs)
  | k /= 0 = Just ( lcm k lcmCoeff
                  , lcmDiv
                  , AtomCt pol op x (div lcmCoeffFinal k |*| (rhs - lRest))
                  )
  where
  (k, lRest) = tSplitVar x lhs

-- Does it occur on the right?
aCt x lcmCoeffFinal lcmCoeff lcmDiv (Atom pol op lhs rhs)
  | k /= 0 = Just ( lcm k lcmCoeff
                  , lcmDiv
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
aCt x lcmCoeffFinal lcmCoeff lcmDiv (Div p m t)
  | k /= 0  = let sc = div lcmCoeffFinal k
                  m1 = abs (m * sc)
              in Just ( lcm lcmCoeff k
                      , lcm lcmDiv m1
                      , DivCt p m1 x (sc |*| rest)
                      )
  where (k,rest) = tSplitVar x t

-- It does not occur anywhere.
aCt _ _ _ _ _ = Nothing


{-| Normalize a formula with respect to a particular variable.
In the resulting formula, the variable (technically, a new variable with
the same name) has coefficient 1.
Example: @2x > 5 --> x > 10@

As a result we return:
    * the LCM of all coefficients of the variables,
    * the LCM of all divisors where the (new) variable is mentioned,
    * Parts of the formula that do not mention the variable are
      tagged with 'Fo'.
-}
aCts :: Name -> Formula -> (Integer, Integer, CtFo)
aCts x form = res
  where
  res@(lcmCoeffFinal,_,_) = go True 1 1 form

  {- The boolean paramter to 'go' indicates if we should try the equality
     optimization. We implement this in `tryEqOpt` which flattens
     a conjunction and looks for equalities.  If we don't find any equalities,
     we go back to the `go` function, but now we disable the optimization,
     to avoid an infinite loop.   The optimization is autmoatically re-enabled
     when we go under a disjunction.
  -}

  go _ lcmCoeff lcmDiv f@(AtomF a) =
    case aCt x lcmCoeffFinal lcmCoeff lcmDiv a of -- RECURSION: cf lcmCoeffFinal
      Just (lcmCoeff', lcmDiv', ct) -> (lcmCoeff', lcmDiv', CtAtomF ct)
      Nothing                       -> (lcmCoeff,  lcmDiv,  Fo f)

  -- Try equality optimization.
  go True lcmCoeff lcmDiv f@(ConnF And _ _) = tryEqOpt lcmCoeff lcmDiv f

  go _ lcmCoeff lcmDiv f@(ConnF c l r) =
    case go (c == Or) lcmCoeff lcmDiv l of
      (lcmCoeff1, lcmDiv1, l') ->
         case go (c == Or) lcmCoeff1 lcmDiv1 r of
           (lcmCoeff2, lcmDiv2, r') ->
              case (l',r') of
                (Fo _,Fo _) -> (lcmCoeff, lcmDiv, Fo f)
                _           -> (lcmCoeff2, lcmDiv2, mkConn c l' r')

  -- Construct formulas so that parts that do not mention the quantified
  -- variabele float to the front.
  mkConn c (Fo lf) (CtConnF c' (Fo rf) rest)
    | c == c'           = CtConnF c (Fo (ConnF c lf rf)) rest

  mkConn c (CtConnF c' (Fo lf) rest) (Fo rf)
    | c == c'           = CtConnF c (Fo (ConnF c lf rf)) rest

  mkConn c (CtConnF c' (Fo lf) rest) (CtConnF c'' (Fo rf) rest')
    | c == c' && c == c'' = CtConnF c (Fo (ConnF c lf rf))
                                      (CtConnF c rest rest')

  mkConn c lf rf@(Fo _) = CtConnF c rf lf

  mkConn c lf rf        = CtConnF c lf rf

  {- The Equality Optmization

  We look for pattrens of the form:                `x = t /\ P`.
  When we spot this pattern, we can continue with: `x = t /\ P (t/x)`.

  The benfit of this is that now `P` does not mention `x`, which results
  in less work when eliminating quantifiers (e.g., `lcmDiv` will be smaller). -}

  tryEqOpt lcmCoeff lcmDiv fo
    = let (eqs,others) = partition (isEq x) (splitAnd fo)
      in case eqs of
           AtomF a : more ->
             -- RECURSIONL cf. lcmCoeffFinal
             let Just (lcmCoeff', _, a') = aCt x lcmCoeffFinal lcmCoeff lcmDiv a
             in (lcmCoeff', lcmDiv, mkAnd a' (more ++ others))
           _ -> go False lcmCoeff lcmDiv fo

  -- Construct formula when equality optimization kicked in.
  mkAnd a [] = CtAtomF a
  mkAnd a fs =
    let AtomCt _ _ _ t = a
    in CtConnF And (Fo $ foldl1 (ConnF And) $ map (fLet x t) fs) (CtAtomF a)

-- | Is this an equality constraint for the given variable?
isEq :: Name -> Formula -> Bool
isEq x (AtomF (Atom Pos Eq lhs rhs)) = tCoeff x lhs /= 0 || tCoeff x rhs /= 0
isEq _ _ = False

-- | Split a formula into its conjuncts.  Always returns at least one element.
splitAnd :: Formula -> [Formula]
splitAnd f0 = go f0 []
  where
  go (ConnF And f1 f2) more = go f1 (go f2 more)
  go f more                 = f : more

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
negInfAtom :: Integer -> Ct -> Atom
negInfAtom _ (AtomCt pol op _ _) = Bool $ evalPol pol $ case op of
                                                          Eq  -> False
                                                          Lt  -> True
                                                          Leq -> True
negInfAtom j (DivCt pol m _ t)   = Div pol m (j |+| t)


-- | Case when variable gets arbitrarily large.
posInfAtom :: Integer -> Ct -> Atom
posInfAtom _ (AtomCt pol _ _ _) = Bool $ case pol of
                                           Pos -> False -- eq,lt,leq: all False
                                           Neg -> True  -- negations are true
posInfAtom j (DivCt p m _ t)    = Div p m (j |+| t)

-- | Replace the variable in a constraint with the given term.
letAtom :: Term -> Ct -> Atom
letAtom b (AtomCt pol op _ rhs) = mkAtom pol op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b)
letAtom b (DivCt p m _ t) = mkDiv p m (b + t)



-- XXX:
-- Optimization 2: When we are eliminating top-level quantifiers,
-- we don't need to do all of [ 1 .. delta ]

ex :: Name -> Formula -> Formula
ex x (ConnF Or f1 f2) = ConnF Or (ex x f1) (ex x f2)
ex x fo =
  let (_coeff, delta, ctFo) = aCts x fo
      mkOr = ConnF Or
      mk :: [Formula] -> [Formula] -> Formula
      mk xs [] = foldr1 mkOr xs
      mk [] ys = foldr1 mkOr ys
      mk xs ys = mkOr (foldr1 mkOr xs) (foldr1 mkOr ys)
  in case ctFo of
       Fo f -> f -- Did not mention variable, nothing to do.
       _    ->
         case getBounds (getCts ctFo []) of
           Left lowerBounds  ->
             mk [ ctAtoms (negInfAtom j) ctFo
                | j <- [ 1 .. delta ] ]

                [ ctAtoms (letAtom (j |+| b)) ctFo
                | j <- [ 1 .. delta ], b <- lowerBounds ]

           Right upperBounds ->
            mk [ ctAtoms (posInfAtom (negate j)) ctFo
               | j <- [ 1 .. delta ] ]

               [ ctAtoms (letAtom (negate j |+| a)) ctFo
               | j <- [ 1 .. delta ], a <- upperBounds ]

exists :: [Name] -> Formula -> Formula
exists ns fo = foldr ex fo ns



--------------------------------------------------------------------------------
-- Evaluation.

-- | Check if a statement with no free variables is true.
isTrue :: Formula -> Maybe Bool
isTrue fo =
  case fo of
    ConnF c f1 f2 -> evalConn c (isTrue f1) (isTrue f2)
    AtomF a       -> evalAtom a

evalAtom :: Atom -> Maybe Bool
evalAtom (Div p m t) = evalPolMb p $
                       if m == 1 then Just True
                                 else do x <- evalTerm t
                                         return (mod x m == 0)
evalAtom (Bool b) = Just b
evalAtom (Atom pol op lhs rhs) =
  evalPolMb pol $
  case op of
    Lt  -> liftM2 (<)  (evalTerm lhs) (evalTerm rhs)
    Leq -> liftM2 (<=) (evalTerm lhs) (evalTerm rhs)
    Eq  -> liftM2 (==) (evalTerm lhs) (evalTerm rhs)

evalTerm :: Term -> Maybe Integer
evalTerm t = isConst t

evalConn :: Conn -> Maybe Bool -> Maybe Bool -> Maybe Bool
evalConn And (Just False) _ = Just False
evalConn And _            y = y

evalConn Or  (Just True) _  = Just True
evalConn Or  _           y  = y

evalPolMb :: Pol -> Maybe Bool -> Maybe Bool
evalPolMb p mb = fmap (evalPol p) mb

evalPol :: Pol -> Bool -> Bool
evalPol Pos x = x
evalPol Neg x = not x


--------------------------------------------------------------------------------
-- Pretty printing.

instance Show Atom where
  showsPrec p a cs = show (ppPrec p a) ++ cs

instance PP Atom where
  ppPrec _ (Atom pol op lhs rhs) = char '"' <>
                                pp lhs <+> text o <+> pp rhs <> char '"'
    where o = case pol of
                Pos ->
                  case op of
                    Lt  -> "<"
                    Leq -> "<="
                    Eq  -> "=="
                Neg ->
                  case op of
                    Leq -> ">"
                    Lt  -> ">="
                    Eq  -> "/="

  ppPrec _ (Bool x) = text (if x then "True" else "False")

  ppPrec _ (Div p x t) = ppPol p
                       $ char '"' <> integer x <+> text "|" <+> pp t <> char '"'

ppPol :: Pol -> Doc -> Doc
ppPol Pos x = x
ppPol Neg x = text "Not" <+> parens x


instance Show Formula where
  showsPrec p f = showsPrec p (toFF f)

-- For printing
data FF = FF Conn [FF] | FFAtom Atom
            deriving Show

toFF :: Formula -> FF
toFF fo =
  case fo of
    AtomF a     -> FFAtom a
    ConnF c _ _ -> FF c $ map toFF $ gather c fo []
  where
  gather c (ConnF c' f1 f2) more
    | c == c'  = gather c f1 (gather c f2 more)
  gather _ f more = f : more


