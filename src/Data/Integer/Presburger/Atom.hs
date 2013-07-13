{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}
module Data.Integer.Presburger.Atom where

import Data.Integer.Presburger.Term
import Data.Integer.Presburger.Div as Div
import Data.Integer.Presburger.JList1
import Text.PrettyPrint
import Data.Either(rights)


data Atom   = Atom !Op Term Term
            | Bool Bool

data Op     = Eq | Neq | Lt | Leq | Gt | Geq

data F      = F [(Name,Integer)] (JList Atom) [DivCt]
                deriving Show




instance Show Atom where
  showsPrec p a cs = show (ppPrec p a) ++ cs

instance PP Atom where
  ppPrec _ (Atom op lhs rhs) = char '"' <>
                                pp lhs <+> text o <+> pp rhs <> char '"'
    where o = case op of
                Lt  -> "<"
                Leq -> "<="
                Gt  -> ">"
                Geq -> "=>"
                Eq  -> "=="
                Neq -> "/="

  ppPrec _ (Bool x) = text (if x then "True" else "False")

type Ct = Atom

{- | Transform atom so that variable is on the LHS with coefficient 1.
If the variable is not mentioned in the atom, then it is left unchanged,
and tagged with @Left@. Otherwise, we return the variable's current
coefficient and the normalized constraint. -}
aCt :: Name    ->   -- ^ Variable.
       Integer ->   -- ^ LCM of all coefficients for the variable (LAZY).
       Atom    ->   -- ^ Constraint to be normalizied.
       Either Atom (Integer, Ct)
aCt x c (Atom op lhs rhs)
  | lC /= 0 = Right ( lC, Atom op (tVar x) (div c lC |*| (rhs - lRest)) )
  where
  (lC, lRest) = tSplitVar x lhs

aCt x c (Atom op lhs rhs)
  | rC /= 0 = Right ( rC, Atom newOp (tVar x) (div c rC |*| (lhs - rRest)) )
  where
  (rC, rRest) = tSplitVar x rhs
  newOp = case op of
            Lt  -> Gt
            Leq -> Geq
            Gt  -> Lt
            Geq -> Leq
            Eq  -> Eq
            Neq -> Neq


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
  go !d !ls !us (Atom op _ rhs : more) =
    case op of
      Lt  -> go (d+1) ls             (rhs : us)     more
      Gt  -> go (d-1) (rhs : ls)     us             more
      Leq -> go (d+1) ls             (rhs + 1 : us) more
      Geq -> go (d-1) (rhs - 1 : ls) us             more
      Eq  -> go d     (rhs - 1 : ls) (rhs + 1 : us) more
      Neq -> go d     (rhs : ls)     (rhs : us)     more

  go d ls us (Bool _ : more) = go d ls us more
  go d ls us []              = if d >= 0 then Left ls else Right us


-- | Value of constraint as variable get arbitrarily small.
negInfAtom :: Ct -> Atom
negInfAtom a@(Bool _)    = a
negInfAtom (Atom op _ _) = Bool $ case op of
                                    Eq  -> False
                                    Neq -> True
                                    Lt  -> True
                                    Leq -> True
                                    Gt  -> False
                                    Geq -> False

-- x |-> x
negInfDiv :: Bool -> Name -> DivCt -> DivCt
negInfDiv False _ ct   = ct
negInfDiv True x (m,t) = (m, tLet x 1 t)

-- x |-> x + b
lowerBoundedAtom :: Bool -> Term -> Ct -> Atom
lowerBoundedAtom o b (Atom op lhs rhs) = Atom op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b - var)
        var = if o then 1 else lhs
lowerBoundedAtom _ _ (Bool _) = error "lowerBoundedAtom on Bool"

-- x |-> x + b
lowerBoundedDivCt :: Bool -> Name -> Term -> DivCt -> DivCt
lowerBoundedDivCt o x b (m,t) = (m, t' + b)
  where t' = if o then tLet x 1 t else t




-- | Value of constraint as variable gets arbitrarily large
posInfAtom :: Ct -> Atom
posInfAtom a@(Bool _)  = a
posInfAtom (Atom op _ _) = Bool $ case op of
                                    Eq  -> False
                                    Neq -> True
                                    Lt  -> False
                                    Leq -> False
                                    Gt  -> True
                                    Geq -> True

-- x |-> -x
posInfDiv :: Bool -> Name -> DivCt -> DivCt
posInfDiv o x (m,t) = (m, tLet x (negate var) t)
  where var = if o then 1 else tVar x


-- x |-> b - x
upperBoundedAtom :: Bool -> Term -> Ct -> Atom
upperBoundedAtom o b (Atom op lhs rhs) = Atom op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b + var)
        var = if o then 1 else lhs
upperBoundedAtom _ _ (Bool _) = error "upperBoundedAtom on Bool"

-- x |-> b - x
upperBoundedDivCt :: Bool -> Name -> Term -> DivCt -> DivCt
upperBoundedDivCt o x b (m,t) = (m, tLet x (b - var) t)
  where var = if o then 1 else tVar x



-- | Eliminate an existentially quantified variable.
ex :: Name -> F -> [F]
ex x fo@(F ds as cs) =
  let (c, as1, cs1) = aCts x as cs
      trivial       = fold (\e m -> isLeft e && m) as1 (all isLeft cs1)

      -- add new divisibilty constraint, unless boring.
      newCs         = if c == 1 then cs1 else Right (c, tVar x) : cs1
      delta         = foldr lcm' 1 newCs
      justOne       = delta == 1


      newDs         = if justOne then ds else (x,delta) : ds

      mkF af cf     = F newDs (fromRight af as1) (fromRight cf newCs)

      negF          = mkF negInfAtom (negInfDiv justOne x)
      lBound b      = mkF (lowerBoundedAtom justOne b)
                          (lowerBoundedDivCt justOne x b)
      posF          = mkF posInfAtom (posInfDiv justOne x)
      uBound b      = mkF (upperBoundedAtom justOne b)
                          (upperBoundedDivCt justOne x b)

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
check (F ds as cs) = go [] (Div.solve ds cs)
  where
  go x (su : sus) = fmap (evalAtom su) as : go x sus
  go _ []         = []
{-
  go solns [] = solns
  go solns (su : sus) =
    let new = fmap (evalAtom su) as
    in if isTop new then [new] else go (addSoln new solns) sus
-}

  evalTerm su t = case isConst (Div.instTerm su t) of
                    Just n  -> n
                    Nothing -> error "Unbound free variable."

  evalAtom _ (Bool b) = b
  evalAtom su (Atom op lhs rhs) =
    case op of
      Lt  -> evalTerm su lhs <  evalTerm su rhs
      Leq -> evalTerm su lhs <= evalTerm su rhs
      Gt  -> evalTerm su lhs >  evalTerm su rhs
      Geq -> evalTerm su lhs >= evalTerm su rhs
      Eq  -> evalTerm su lhs == evalTerm su rhs
      Neq -> evalTerm su lhs /= evalTerm su rhs

isTop :: JList Bool -> Bool
isTop (One x)     = x
isTop (Two xs ys) = isTop xs && isTop ys

-- | Check to see if one of the solutions implies the other.
-- Smaller implies larger
merge :: JList Bool -> JList Bool -> Maybe Ordering
merge as bs = go EQ (toList as) (toList bs)
  where
  go d (x : xs) (y : ys)
    | x == y    = go d xs ys
    | x <  y    = if d == GT then Nothing else go LT xs ys
    | otherwise = if d == LT then Nothing else go GT xs ys
  go d [] []    = Just d
  go _ _ _      = Nothing -- different lengths, should not happen


addSoln :: JList Bool -> [JList Bool] -> [JList Bool]
addSoln new [] = [new]
addSoln new (cur : more) =
  case merge new cur of
    Nothing -> cur : addSoln new more
    Just EQ -> cur : more
    Just LT -> cur : more
    Just GT -> addSoln new more



