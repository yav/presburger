{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}
module Data.Integer.Presburger.Atom where

import Data.Integer.Presburger.Term
import Data.Integer.Presburger.Div as Div
import Data.Integer.Presburger.JList1
import Text.PrettyPrint
import Data.Either(rights)



data Atom   = Atom !Pol !Pred Term Term
            | Div !Pol !Integer Term
            | Bool Bool
              deriving Eq

data Pol    = Pos | Neg
              deriving Eq

data Pred   = Eq | Lt | Leq
              deriving Eq

data F      = F [(Name,Integer)] (JList Atom) [DivCt]
                deriving Show

instance Show Atom where
  showsPrec p a cs = show (ppPrec p a) ++ cs

instance PP Atom where
  ppPrec _ (Atom pol op lhs rhs) = char '"' <>
                                pp lhs <+> text o <+> pp rhs <> char '"'
    where o = case (pol,op) of
                (Pos,Lt)  -> "<"
                (Pos,Leq) -> "<="
                (Pos,Eq)  -> "=="
                (Neg,Leq) -> ">"
                (Neg,Lt)  -> "=>"
                (Neg,Eq)  -> "/="

  ppPrec _ (Bool x) = text (if x then "True" else "False")

  ppPrec _ (Div p x t) = ppPol p
                       $ char '"' <> integer x <+> text "|" <+> pp t <> char '"'

ppPol :: Pol -> Doc -> Doc
ppPol Pos x = x
ppPol Neg x = text "Not" <+> parens x

type Ct = Atom

{- | Transform atom so that variable is on the LHS with coefficient 1.
If the variable is not mentioned in the atom, then it is left unchanged,
and tagged with @Left@. Otherwise, we return the variable's current
coefficient and the normalized constraint. -}
aCt :: Name    ->   -- ^ Variable.
       Integer ->   -- ^ LCM of all coefficients for the variable (LAZY).
       Atom    ->   -- ^ Constraint to be normalizied.
       Either Atom (Integer, Ct)
aCt x c (Atom pol op lhs rhs)
  | lC /= 0 = Right ( lC, Atom pol op (tVar x) (div c lC |*| (rhs - lRest)) )
  where
  (lC, lRest) = tSplitVar x lhs

aCt x c (Atom pol op lhs rhs)
  | rC /= 0 = Right ( rC, Atom newP newOp (tVar x) (div c rC |*| (lhs - rRest)) )
  where
  (rC, rRest) = tSplitVar x rhs
  (newP,newOp) = case (pol,op) of
                   (Pos,Eq)  -> (Pos,Eq)
                   (Pos,Lt)  -> (Neg,Leq)
                   (Pos,Leq) -> (Neg,Lt)
                   (Neg,Eq)  -> (Neg,Eq)
                   (Neg,Lt)  -> (Pos,Leq)
                   (Neg,Leq) -> (Pos,Lt)

aCt x c (Div p m t)
  | coeff /= 0  = let sc = div c coeff
                  in Right (coeff, Div p (abs (m * sc)) (tVar x + sc |*| rest))
  where (coeff,rest) = tSplitVar x t

aCt _ _ a = Left a

-- | Normalize a divisibility constraint, so that coefficient
-- of the variable is 1.
aDivCt :: Name -> Integer -> DivCt -> Either DivCt (Integer, DivCt)
aDivCt x c (m,t)
  | coeff /= 0  = let sc = div c coeff
                  in Right (coeff, (abs (m * sc), tVar x + sc |*| rest))
  where (coeff,rest) = tSplitVar x t

aDivCt _ _ d = Left d


-- | Normalize a formula with respect to a particular variable.
-- In the resulting formula, the variable has coefficient 1
-- Example: @2x > 5 --> x > 10@
aCts :: Name -> JList Atom -> [DivCt] ->
              (Integer, JList (Either Atom Ct), [Either DivCt DivCt])
aCts x as ds =
  let mbCts = fmap (aCt x c) as
      mbDs  = map (aDivCt x c) ds
      c     = fold lcm' mbCts (foldr lcm' 1 mbDs)

  in (c, mapRight snd mbCts, mapRight snd mbDs)
  where
  mapRight f               = fmap (either Left (Right . f))

-- A variation on `lcm` to match the shape of inputs we work with.
lcm' :: Either a (Integer,b) -> Integer -> Integer
lcm' (Right (coeff,_)) l = lcm coeff l
lcm' (Left _)          l = l


-- Left: there were fewer lower bounds, Right: fewer upper bounds
getBounds :: [Ct] -> Either [Term] [Term]
getBounds = go (0::Int) [] []
  where
  go !d !ls !us (Atom pol op _ rhs : more) =
    case (pol,op) of
      (Pos,Lt ) -> go (d+1) ls             (rhs : us)     more
      (Neg,Leq) -> go (d-1) (rhs : ls)     us             more
      (Pos,Leq) -> go (d+1) ls             (rhs + 1 : us) more
      (Neg,Lt ) -> go (d-1) (rhs - 1 : ls) us             more
      (Pos,Eq ) -> go d     (rhs - 1 : ls) (rhs + 1 : us) more
      (Neg,Eq ) -> go d     (rhs : ls)     (rhs : us)     more

  go d ls us (Bool _ : more) = go d ls us more
  go d ls us (Div {} : more) = go d ls us more
  go d ls us []              = if d >= 0 then Left ls else Right us


-- | Value of constraint as variable gets arbitrarily small.
negInfAtom :: Ct -> Atom
negInfAtom a@(Bool _)    = a
negInfAtom (Atom pol op _ _) = Bool $ evalPol pol $ case op of
                                                      Eq  -> False
                                                      Lt  -> True
                                                      Leq -> True
negInfAtom a@(Div {})   = a

-- x |-> x + b
lowerBoundedAtom :: Term -> Ct -> Atom
lowerBoundedAtom b (Atom pol op lhs rhs) = Atom pol op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b - lhs)
lowerBoundedAtom b (Div p m t)= Div p m (t + b)
lowerBoundedAtom _ (Bool _)   = error "lowerBoundedAtom on Bool"




-- | Value of constraint as variable gets arbitrarily large
posInfAtom :: Name -> Ct -> Atom
posInfAtom _ a@(Bool _)    = a
posInfAtom _ (Atom pol _ _ _) = Bool $ case pol of
                                         Pos -> False
                                         Neg -> True
posInfAtom x (Div p m t)     = Div p m (tLet x (negate (tVar x)) t)


-- x |-> b - x
upperBoundedAtom :: Name -> Term -> Ct -> Atom
upperBoundedAtom _ b (Atom pol op lhs rhs) = Atom pol op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b + lhs)
upperBoundedAtom x b (Div p m t) = Div p m (tLet x (b - tVar x) t)
upperBoundedAtom _ _ (Bool _) = error "upperBoundedAtom on Bool"





-- x |-> b - x
upperBoundedDivCt :: Name -> Term -> DivCt -> DivCt
upperBoundedDivCt x b (m,t) = (m, tLet x (b - var) t)
  where var = tVar x

-- x |-> -x
posInfDiv :: Name -> DivCt -> DivCt
posInfDiv x (m,t) = (m, tLet x (negate var) t)
  where var = tVar x

-- x |-> x + b
lowerBoundedDivCt :: Name -> Term -> DivCt -> DivCt
lowerBoundedDivCt x b (m,t) = (m, t + b)

-- x |-> x
negInfDiv :: Name -> DivCt -> DivCt
negInfDiv _ ct   = ct



-- | Eliminate an existentially quantified variable.
ex :: Name -> F -> [F]
ex x fo@(F ds as cs) =
  let (c, as1, cs1) = aCts x as cs
      trivial       = fold (\e m -> isLeft e && m) as1 (all isLeft cs1)

      -- add new divisibilty constraint, unless boring.
      newCs         = if c == 1 then cs1 else Right (c, tVar x) : cs1
      delta         = foldr lcm' 1 newCs

      newDs         = if delta == 1 then ds else (x,delta) : ds

      mkF af cf     = F newDs (fromRight af as1) (fromRight cf newCs)

      negF          = mkF negInfAtom (negInfDiv x)
      lBound b      = mkF (lowerBoundedAtom b)
                          (lowerBoundedDivCt x b)
      posF          = mkF (posInfAtom x) (posInfDiv x)
      uBound b      = mkF (upperBoundedAtom x b)
                          (upperBoundedDivCt x b)

  in if trivial
     then [fo]
     else case getBounds (rights (toList as1)) of
            Left bs  -> negF : map lBound bs
            Right bs -> posF : map uBound bs

  where
  fromRight f = fmap (either id f)

  isLeft (Left _) = True
  isLeft _        = False

exists :: [Name] -> F -> [F]
exists ns = go ns
  where
  go (x : xs) f = [ r | f1 <- go xs f, r <- ex x f1 ]
  go [] f = [f]


check :: F -> [JList Bool]
check (F ds as cs) = map (\su -> fmap (evalAtom su) as) (Div.solve ds cs)
  where
  evalTerm su t = case isConst (Div.instTerm su t) of
                    Just n  -> n
                    Nothing -> error "Unbound free variable."

  evalAtom su (Div p m t) = evalPol p (m == 1 || mod (evalTerm su t) m == 0)
  evalAtom _ (Bool b) = b
  evalAtom su (Atom pol op lhs rhs) =
    evalPol pol $
    case op of
      Lt  -> evalTerm su lhs <  evalTerm su rhs
      Leq -> evalTerm su lhs <= evalTerm su rhs
      Eq  -> evalTerm su lhs == evalTerm su rhs

evalPol :: Pol -> Bool -> Bool
evalPol Pos x = x
evalPol Neg x = not x





