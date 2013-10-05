{-# LANGUAGE Safe #-}
module Data.Integer.Presburger.Formula
  ( Formula
  , fConn
  , fConns
  , fAtom
  , fLet
  , fNeg
  , Conn(..)
  , Pol(..)
  , PredS(..)
  , Atom
  , mkAtom
  , mkDiv
  , mkBool
  , isFConn, isFAtom, splitConn
  , isAtom, isDiv, isBool
  , evalPol
  )
  where

import Data.Integer.Presburger.Term
  (Term, Name, PP(..), pp, tLet, tSplit, isConst)

import Text.PrettyPrint
import Control.Monad(liftM2)

-- | Formulas.
data Formula  = AtomF Atom
              | ConnF !Conn Formula Formula

-- | Connectives.
data Conn     = And | Or
                deriving (Show, Eq)


-- | Basic propositions.
data Atom     = Atom !Pol !PredS Term Term  -- ^ Comparisons
              | Div  !Pol !Integer Term     -- ^ Divisibility assertions
              | Bool !Bool                  -- ^ Constants
                deriving Eq

-- | Polarity of atoms.
data Pol      = Pos     -- ^ Normal atom.
              | Neg     -- ^ Negated atom.
                deriving (Eq, Show)

-- | Binary predicate symbols.
data PredS    = Eq | Lt | Leq
                deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Patterns

isFAtom :: Formula -> Maybe Atom
isFAtom (AtomF a)     = Just a
isFAtom _             = Nothing

isFConn :: Formula -> Maybe (Conn, Formula, Formula)
isFConn (ConnF c p q) = Just (c,p,q)
isFConn _             = Nothing

-- | Split a formula into its conjuncts.  Always returns at least one element.
splitConn :: Conn -> Formula -> [Formula]
splitConn c0 f0 = go f0 []
  where
  go (ConnF c f1 f2) more | c == c0 = go f1 (go f2 more)
  go f more                         = f : more



--------------------------------------------------------------------------------
-- Smart constructors.

fConns :: Conn -> [Formula] -> Formula
fConns And [] = fAtom $ mkBool True
fConns Or  [] = fAtom $ mkBool False
fConns c fs   = foldr1 (fConn c) fs

fConn :: Conn -> Formula -> Formula -> Formula

-- NOTE: Here we only simply True/False when it appears in the first argument.
-- This memory leaks where we have to fullly evaluate both sub-formulas
-- before we know the top-most connective in the formula.
fConn And f1@(AtomF (Bool False)) _   = f1
fConn And    (AtomF (Bool True))  f2  = f2

fConn Or  f1@(AtomF (Bool True))  _   = f1
fConn Or     (AtomF (Bool False)) f2  = f2

fConn c f1 f2                         = ConnF c f1 f2

fAtom :: Atom -> Formula
fAtom = AtomF

fNeg :: Formula -> Formula
fNeg (ConnF c f1 f2) = ConnF (negC c) (fNeg f1) (fNeg f2)
  where
  negC And                  = Or
  negC Or                   = And

fNeg (AtomF a)       = AtomF (negA a)
  where
  negP Pos                  = Neg
  negP Neg                  = Pos

  negA (Bool b)             = Bool (not b)
  negA (Atom pol op t1 t2)  = Atom (negP pol) op t1 t2
  negA (Div  pol m t)       = Div  (negP pol) m t


fLet :: Name -> Term -> Formula -> Formula
fLet x t fo =
  case fo of
    ConnF c f1 f2 -> fConn c (fLet x t f1) (fLet x t f2)
    AtomF a ->
      case a of
        Atom p s t1 t2 ->
          let (lhs,rhs) = tSplit $ tLet x t $ t2 - t1
          in AtomF (mkAtom p s lhs rhs)
        Div  p m t1    -> AtomF (mkDiv p m (tLet x t t1))
        Bool _         -> fo


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

mkBool :: Bool -> Atom
mkBool = Bool

isAtom :: Atom -> Maybe (Pol, PredS, Term, Term)
isAtom (Atom p s x y) = Just (p,s,x,y)
isAtom _              = Nothing

isDiv :: Atom -> Maybe (Pol, Integer, Term)
isDiv (Div p m t) = Just (p,m,t)
isDiv _           = Nothing

isBool :: Atom -> Maybe Bool
isBool (Bool a) = Just a
isBool _        = Nothing


--------------------------------------------------------------------------------
-- Evaluation.

evalAtom :: Atom -> Maybe Bool
evalAtom (Div p m t) = evalPolMb p $
                       if m == 1 then Just True
                                 else do x <- isConst t
                                         return (mod x m == 0)
evalAtom (Bool b) = Just b
evalAtom (Atom pol op lhs rhs) =
  evalPolMb pol $
  case op of
    Lt  -> liftM2 (<)  (isConst lhs) (isConst rhs)
    Leq -> liftM2 (<=) (isConst lhs) (isConst rhs)
    Eq  -> liftM2 (==) (isConst lhs) (isConst rhs)

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

    where ppPol Pos d = d
          ppPol Neg d = text "Not" <+> parens d

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


