{-# LANGUAGE RecordWildCards, BangPatterns #-}
module Atom where

import Term
import GCD
import JList1
import Text.PrettyPrint
import Data.Either(rights)


data Atom   = Atom { aOp :: !Op, aLhs :: Term, aRhs :: Term }
            | Bool Bool

data Op     = Eq | Neq | Lt | Leq | Gt | Geq

data F      = F [(Name,Integer)] (JList Atom) [DivCt]
                deriving Show




instance Show Atom where
  showsPrec p a cs = show (ppPrec p a) ++ cs

instance PP Atom where
  ppPrec _ Atom { .. } = pp aLhs <+> text o <+> pp aRhs
    where o = case aOp of
                Lt  -> "<"
                Leq -> "<="
                Gt  -> ">"
                Geq -> "=>"
                Eq  -> "=="
                Neq -> "/="

  ppPrec _ (Bool x) = text $ if x then "True" else "False"

type Ct = Atom

aCt :: Name -> Integer -> Atom -> Either Atom (Integer, Ct)
aCt x c Atom { .. }
  | lC /= 0 = Right ( lC
                   , Atom { aLhs = tVar x
                          , aRhs = tMul (div c lC) (aRhs - lRest)
                          , .. })
  where
  (lC, lRest) = tSplitVar x aLhs
aCt x c Atom { .. }
  | rC /= 0 = Right ( rC
                   , Atom { aLhs = tVar x
                          , aRhs = tMul (div c rC) (aLhs - rRest)
                          , aOp  = case aOp of
                                     Lt  -> Gt
                                     Leq -> Geq
                                     Gt  -> Lt
                                     Geq -> Leq
                                     Eq  -> Eq
                                     Neq -> Neq })
  where
  (rC, rRest) = tSplitVar x aRhs

aCt _ _ a = Left a

aDivCt :: Name -> Integer -> DivCt -> Either DivCt (Integer, DivCt)
aDivCt x c (m,t)
  | coeff /= 0  = let sc = div c coeff
                  in Right (coeff, (abs (m * sc), tVar x + tMul sc rest))
  where (coeff,rest) = tSplitVar x t

aDivCt _ _ d = Left d





aCts :: Name -> JList Atom -> [DivCt] ->
              (Integer, JList (Either Atom Ct), [Either DivCt DivCt])
aCts x as ds =
  let mbCts = fmap (aCt x c) as
      mbDs  = map (aDivCt x c) ds
      cs    = map fst (rights mbDs) ++ map fst (rights $ toList mbCts)
      c     = if null cs then 1 else foldr1 lcm cs
  in (c, mapRight snd mbCts, mapRight snd mbDs)
  where
  mapRight f = fmap (either Left (Right . f))

-- Left: there were fewer lower bounds, Right: fewer upper bounds
getBounds :: [Ct] -> Either [Term] [Term]
getBounds = go (0::Int) [] []
  where
  go !d !ls !us (Atom { .. } : more) =
    case aOp of
      Lt  -> go (d+1) ls              (aRhs : us)     more
      Gt  -> go (d-1) (aRhs : ls)     us              more
      Leq -> go (d+1) ls              (aRhs + 1 : us) more
      Geq -> go (d-1) (aRhs - 1 : ls) us              more
      Eq  -> go d     (aRhs - 1 : ls) (aRhs + 1 : us) more
      Neq -> go d     (aRhs : ls)     (aRhs : us)     more

  go d ls us (Bool _ : more) = go d ls us more
  go d ls us []              = if d >= 0 then Left ls else Right us


-- | Value of constraint as variable get arbitrarily small.
negInfAtom :: Ct -> Atom
negInfAtom a@(Bool _)  = a
negInfAtom Atom { .. } = Bool $ case aOp of
                                  Eq  -> False
                                  Neq -> True
                                  Lt  -> True
                                  Leq -> True
                                  Gt  -> False
                                  Geq -> False

-- x |-> x
negInfDiv :: DivCt -> DivCt
negInfDiv = id

-- x |-> x + b
lowerBoundedAtom :: Term -> Ct -> Atom
lowerBoundedAtom b Atom { .. } = Atom { aLhs = newLhs, aRhs = newRhs, .. }
  where (newLhs,newRhs) = tSplit (aRhs - b - aLhs)
lowerBoundedAtom _ (Bool _) = error "lowerBoundedAtom on Bool"

-- x |-> x + b
lowerBoundedDivCt :: Term -> DivCt -> DivCt
lowerBoundedDivCt b (m,t) = (m, t + b)

-- | Value of constraint as variable gets arbitrarily large
posInfAtom :: Ct -> Atom
posInfAtom a@(Bool _)  = a
posInfAtom Atom { .. } = Bool $ case aOp of
                                  Eq  -> False
                                  Neq -> True
                                  Lt  -> False
                                  Leq -> False
                                  Gt  -> True
                                  Geq -> True

-- x |-> -x
posInfDiv :: Name -> DivCt -> DivCt
posInfDiv x (m,t) = (m, tLet x (negate (tVar x)) t)


-- x |-> b - x
upperBoundedAtom :: Term -> Ct -> Atom
upperBoundedAtom b Atom { .. } = Atom { aLhs = newLhs, aRhs = newRhs, .. }
  where (newLhs,newRhs) = tSplit (aRhs - b + aLhs)
upperBoundedAtom _ (Bool _) = error "upperBoundedAtom on Bool"

-- x |-> b - x
upperBoundedDivCt :: Name -> Term -> DivCt -> DivCt
upperBoundedDivCt x b (m,t) = (m, tLet x (b - tVar x) t)




ex :: Name -> F -> [F]
ex x (F ds as cs) =
  let (c, as1, cs1) = aCts x as cs
      ms            = c : map fst (rights cs1)
      d             = foldr1 lcm ms

      algCts        = rights $ toList as1
      newDs         = (x,d) : ds
      newCs         = Right (c, tVar x) : cs1

      mkF af cf     = F newDs (fromRight af as1) (fromRight cf newCs)

      negF          = mkF negInfAtom negInfDiv
      lBound b      = mkF (lowerBoundedAtom b) (lowerBoundedDivCt b)
      posF          = mkF posInfAtom (posInfDiv x)
      uBound b      = mkF (upperBoundedAtom b) (upperBoundedDivCt x b)

  in case getBounds algCts of
       Left bs  -> negF : map lBound bs
       Right bs -> posF : map uBound bs

  where
  fromRight f = fmap (either id f)

exists :: [Name] -> F -> [F]
exists (x : xs) f = concatMap (exists xs) (ex x f)
exists [] f       = [f]


check :: F -> [JList Bool]
check (F ds as cs) = go [] (GCD.solve ds cs)
  where
  go solns [] = solns
  go solns (su : sus) =
    let new = fmap (evalAtom su) as
    in if isTop new then [new] else go (addSoln new solns) sus

  evalTerm su t = case isConst (GCD.instTerm su t) of
                    Just n  -> n
                    Nothing -> error "Unbound free variable."

  evalAtom _ (Bool b) = b
  evalAtom su Atom { .. } =
    case aOp of
      Lt  -> evalTerm su aLhs <  evalTerm su aRhs
      Leq -> evalTerm su aLhs <= evalTerm su aRhs
      Gt  -> evalTerm su aLhs >  evalTerm su aRhs
      Geq -> evalTerm su aLhs >= evalTerm su aRhs
      Eq  -> evalTerm su aLhs == evalTerm su aRhs
      Neq -> evalTerm su aLhs /= evalTerm su aRhs

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


{-
test = exists ["x","y"] $ F [] [ "x" + 5 * "y" |>| 1, 13 * "x" - "y" |>| 1, "x" + 2 |<| 0 ] []
-}

