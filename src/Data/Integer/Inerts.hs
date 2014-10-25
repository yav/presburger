{-# LANGUAGE Safe #-}
module Data.Integer.Inerts where

import           Data.Integer.Term

import           Data.Maybe ( maybeToList )
import           Data.List ( partition )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Text.PrettyPrint (Doc, (<+>), text, vcat)


-- | The inert set contains the solver's state on one possible path.
data Inerts = Inerts
  { bounds :: Map Name ([Bound],[Bound])
    -- ^ Known lower and upper bounds for variables.
    -- Each bound @(c,t)@ in the first  list asserts that @t < c * x@
    -- Each bound @(c,t)@ in the second list asserts that @c * x < t@

  , solved :: Map Name Term
    -- ^ Definitions for resolved variables.
    -- These form an idempotent substitution.
  } deriving Show




-- | Readable display for the inerts.
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

iBounds :: BoundType -> Name -> Inerts -> [Bound]
iBounds f x is = case Map.lookup x (bounds is) of
                   Nothing -> []
                   Just bs -> case f of
                                Lower -> fst bs
                                Upper -> snd bs

-- | Record a bound for the given variable.
iAddBound :: BoundType -> Name -> Bound -> Inerts -> Inerts
iAddBound bt x b i =
  let entry = case bt of
                Lower -> ([b],[])
                Upper -> ([],[b])
      jn (newL,newU) (oldL,oldU) = (newL++oldL, newU++oldU)
  in i { bounds = Map.insertWith jn x entry (bounds i) }





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


--------------------------------------------------------------------------------
-- Constraints and Bounds on Variables

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

