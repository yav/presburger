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

aCt :: Name -> Integer -> Atom -> Either Atom (Integer, Ct)
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

aDivCt :: Name -> Integer -> DivCt -> Either DivCt (Integer, DivCt)
aDivCt x c (m,t)
  | coeff /= 0  = let sc = div c coeff
                  in Right (coeff, (abs (m * sc), tVar x + sc |*| rest))
  where (coeff,rest) = tSplitVar x t

aDivCt _ _ d = Left d





aCts :: Name -> JList Atom -> [DivCt] ->
              (Integer, JList (Either Atom Ct), [Either DivCt DivCt])
aCts x as ds =
  let mbCts = fmap (aCt x c) as
      mbDs  = map (aDivCt x c) ds
      cs    = map fst (rights mbDs) ++ map fst (rights $ toList mbCts)
      c     = foldr lcm 1 cs
  in (c, mapRight snd mbCts, mapRight snd mbDs)
  where
  mapRight f = fmap (either Left (Right . f))

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
negInfDiv :: DivCt -> DivCt
negInfDiv = id

-- x |-> x + b
lowerBoundedAtom :: Term -> Ct -> Atom
lowerBoundedAtom b (Atom op lhs rhs) = Atom op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b - lhs)
lowerBoundedAtom _ (Bool _) = error "lowerBoundedAtom on Bool"

-- x |-> x + b
lowerBoundedDivCt :: Term -> DivCt -> DivCt
lowerBoundedDivCt b (m,t) = (m, t + b)

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
posInfDiv :: Name -> DivCt -> DivCt
posInfDiv x (m,t) = (m, tLet x (negate (tVar x)) t)


-- x |-> b - x
upperBoundedAtom :: Term -> Ct -> Atom
upperBoundedAtom b (Atom op lhs rhs) = Atom op newLhs newRhs
  where (newLhs,newRhs) = tSplit (rhs - b + lhs)
upperBoundedAtom _ (Bool _) = error "upperBoundedAtom on Bool"

-- x |-> b - x
upperBoundedDivCt :: Name -> Term -> DivCt -> DivCt
upperBoundedDivCt x b (m,t) = (m, tLet x (b - tVar x) t)




ex :: Name -> F -> [F]
ex x fo@(F ds as cs) =
  let (c, as1, cs1) = aCts x as cs
      trivial       = all isLeft (toList as1) && all isLeft cs1

      ms            = c : map fst (rights cs1)
      d             = foldr1 lcm ms

      newDs         = (x,d) : ds
      newCs         = Right (c, tVar x) : cs1

      mkF af cf     = F newDs (fromRight af as1) (fromRight cf newCs)

      negF          = mkF negInfAtom negInfDiv
      lBound b      = mkF (lowerBoundedAtom b) (lowerBoundedDivCt b)
      posF          = mkF posInfAtom (posInfDiv x)
      uBound b      = mkF (upperBoundedAtom b) (upperBoundedDivCt x b)

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


{-
test = exists ["x","y"] $ F [] [ "x" + 5 * "y" |>| 1, 13 * "x" - "y" |>| 1, "x" + 2 |<| 0 ] []
-}

