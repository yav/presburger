{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}
module Data.Integer.Presburger.Atom where

import Data.Integer.Presburger.Term
import Text.PrettyPrint

data Fo     = AtomF Atom
            | ConnF !Conn Fo Fo

data CtFo   = Fo Fo
            | CtConnF !Conn CtFo CtFo
            | CtAtomF Ct

data Conn   = And | Or
              deriving Eq

getCts :: CtFo -> [Ct] -> [Ct]
getCts ctfo more =
  case ctfo of
    Fo _            -> more
    CtConnF _ f1 f2 -> getCts f1 (getCts f2 more)
    CtAtomF ct      -> ct : more

ctAtoms :: (Ct -> Atom) -> CtFo -> Fo
ctAtoms f ctfo =
  case ctfo of
    Fo fo           -> fo
    CtConnF c f1 f2 -> ConnF c (ctAtoms f f1) (ctAtoms f f2)
    CtAtomF ct      -> AtomF (f ct)


fLet :: Name -> Term -> Fo -> Fo
fLet x t fo =
  case fo of
    ConnF c f1 f2 -> ConnF c (fLet x t f1) (fLet x t f2)
    AtomF a ->
      case a of
        Atom p s t1 t2 -> AtomF (Atom p s (tLet x t t1) (tLet x t t2))
        Div  p m t1    -> AtomF (Div  p m (tLet x t t1))
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

XXX: Optimization 1: ex x (x == t /\ P) --> ex x (x == t) /\ P (t/x)
-}
aCts :: Name -> Fo -> (Integer, Integer, CtFo)
aCts x form = res
  where
  res@(lcmCoeffFinal,_,_) = go 1 1 form

  go lcmCoeff lcmDiv f@(AtomF a) =
    case aCt x lcmCoeffFinal lcmCoeff lcmDiv a of -- RECURSION: cf lcmCoeffFinal
      Just (lcmCoeff', lcmDiv', ct) -> (lcmCoeff', lcmDiv', CtAtomF ct)
      Nothing                       -> (lcmCoeff,  lcmDiv,  Fo f)

  go lcmCoeff lcmDiv f@(ConnF c l r) =
    case go lcmCoeff lcmDiv l of
      (lcmCoeff1, lcmDiv1, l') ->
         case go lcmCoeff1 lcmDiv1 r of
           (lcmCoeff2, lcmDiv2, r') ->
              case (l',r') of
                (Fo _,Fo _) -> (lcmCoeff, lcmDiv, Fo f)
                _           -> (lcmCoeff2, lcmDiv2, CtConnF c l' r')


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
                                           Pos -> False -- eq, lt, leq: all False
                                           Neg -> True  -- negations are true
posInfAtom j (DivCt p m _ t)    = Div p m (j |+| t)

-- | Replace the variable in a constraint with the given term.
letAtom :: Term -> Ct -> Atom
letAtom b (AtomCt pol op _ rhs) = Atom pol op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b)
letAtom b (DivCt p m _ t) = Div p m (b + t)



-- XXX:
-- Optimization 2: When we are eliminating top-level quantifiers,
-- we don't need to do all of [ 1 .. delta ]

ex :: Name -> Fo -> Fo
ex x (ConnF Or f1 f2) = ConnF Or (ex x f1) (ex x f2)
ex x fo =
  let (_coeff, delta, ctFo) = aCts x fo
      mkOr = ConnF Or
      mk :: [Fo] -> [Fo] -> Fo
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

exists :: [Name] -> Fo -> Fo
exists ns fo = foldr ex fo ns



--------------------------------------------------------------------------------
-- Evaluation.

check :: Fo -> Bool
check fo =
  case fo of
    ConnF Or  f1 f2 -> check f1 || check f2
    ConnF And f1 f2 -> check f1 && check f2
    AtomF a         -> evalAtom a

evalAtom :: Atom -> Bool
evalAtom (Div p m t) = evalPol p (m == 1 || mod (evalTerm t) m == 0)
evalAtom (Bool b) = b
evalAtom (Atom pol op lhs rhs) =
  evalPol pol $
  case op of
    Lt  -> evalTerm lhs <  evalTerm rhs
    Leq -> evalTerm lhs <= evalTerm rhs
    Eq  -> evalTerm lhs == evalTerm rhs

evalTerm :: Term -> Integer
evalTerm t = case isConst t of
               Just n  -> n
               Nothing -> error "Unbound free variable."

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

