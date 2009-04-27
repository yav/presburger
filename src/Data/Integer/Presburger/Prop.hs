module Data.Integer.Presburger.Prop
  ( module Data.Integer.Presburger.Prop
  , module X
  ) where

import Data.Integer.Presburger.Term as X

-- | Possibly negated propositions.
-- For example, we would express "t1 not equal to t2" like this:
-- @Prop { negated = True, prop = Bin Equal t1 t2 }@
data Prop p   = Prop { negated :: !Bool, prop :: !p }

-- | A proposition normalized with respect to a particular variable.
data NormProp p = Ind (Prop PosP)   -- ^ Independent of variable.
                | Norm (Prop p)     -- ^ Depends on variable.

-- | Basic binary relations.
data RelOp    = Equal | LessThan | LessThanEqual deriving Eq

-- | Basic propositions.
data PosP     = Bin !RelOp Term Term | Divides !Integer Term | FF

-- | Propositions specialized to say something about a particular variable.
data VarP     = NBin !RelOp Term        -- ^ x `op` t
              | NDivides !Integer Term  -- ^ n | x + t

-- | Propositions specialized for a variable with a coefficient.
-- For example: 4 * x = t
-- @CVarP { coeff = 4, pprop = NBin Equal t }@
data CVarP    = CVarP { coeff :: !Integer, pprop :: !VarP }


-- | Rewrite a propositions as a predicate about a specific variable.
norm :: Name -> Prop PosP -> NormProp CVarP
norm x p = case prop p of

  Bin op t1 t2
    | k1 == k2    -> Ind  p    { prop = Bin op t1' t2' }
    | k1 > k2     -> Norm p    { prop = CVarP (k1 - k2) (NBin op (t2' - t1')) }
    | otherwise   -> Norm Prop { prop = CVarP (k2 - k1) (NBin op (t1' - t2'))
                               , negated = if op == Equal then negated p
                                                          else not (negated p)
                               }
    where (k1,t1')  = split_term x t1   -- t1 = k1 * x + t1'
          (k2,t2')  = split_term x t2   -- t2 = k2 * x + t2'

  Divides n t1
    | k1 == 0    -> Ind  p
    | k1 > 0     -> Norm p { prop = CVarP k1 (NDivides n t1') }
    | otherwise  -> Norm p { prop = CVarP (negate k1) (NDivides n (negate t1))}
    where(k1,t1') = split_term x t1     -- t1 = k1 * x + t1'

  FF -> Ind p


-- | Eliminate variable coefficients by scaling the properties appropriately.
scale :: Integer -> Prop CVarP -> Prop VarP
scale k p =
  let np = prop p
      sc = k `div` coeff np
  in p { prop = case pprop np of
                  NBin op t    -> NBin op (sc .* t)
                  NDivides n t -> NDivides (sc * n) (sc .* t)
       }


-- | Evaluate a proposition for a sufficiently small value of
-- the variable, if possible.  Otherwise, substitute the given term.
neg_inf :: Term -> Prop VarP -> Prop PosP
neg_inf t p = case prop p of
  NBin Equal _  -> Prop { negated = negated p, prop = FF }
  NBin _ _      -> Prop { negated = not (negated p), prop = FF }
  NDivides n t1 -> p    { prop = Divides n (t + t1) }

-- | Evaluate a proposition for a sufficiently large value of
-- the variable, if possible.  Otherwise, substitute the given term.
pos_inf :: Term -> Prop VarP -> Prop PosP
pos_inf t p = case prop p of
  NDivides n t1 -> p    { prop = Divides n (t + t1) }
  _             -> Prop { negated = negated p, prop = FF }


-- | Evaluate a proposition with a given term for the variable.
normal :: Term -> Prop VarP -> Prop PosP
normal t p = case prop p of
  NBin op t1    -> p { prop = Bin op t t1 }
  NDivides n t1 -> p { prop = Divides n (t + t1) }


--------------------------------------------------------------------------------

-- | The meanings of atomic propositions
eval_prop :: Prop PosP -> Env -> Bool
eval_prop (Prop neg p) env = if neg then not res else res
  where res = case p of
                FF -> False
                Divides n t  -> divides n (eval_term t env)
                Bin op t1 t2 -> bin_op op (eval_term t1 env) (eval_term t2 env)
                  

bin_op :: RelOp -> Integer -> Integer -> Bool
bin_op op x y = case op of
                  Equal         -> x == y
                  LessThan      -> x < y
                  LessThanEqual -> x <= y

-- | Replace a variable with a constant, in a property.
subst_prop :: Name -> Integer -> Prop PosP -> Prop PosP
subst_prop x n (Prop b p) =
  case p of
    Bin op t1 t2 -> Prop b (Bin op (subst_term x n t1) (subst_term x n t2))
    Divides k t  -> Prop b (Divides k (subst_term x n t))
    FF           -> Prop b FF

simplify_prop :: Prop PosP -> Prop PosP
simplify_prop it@(Prop b p) =
  case p of
    Divides n t -> case is_constant t of
                      Just v -> Prop (b /= divides n v) FF
                      Nothing -> it
    Bin Equal t1 t2 | not b && t1 == t2 -> Prop True FF
    Bin op t1 t2 -> case (is_constant t1, is_constant t2) of
                      (Just v1, Just v2) -> Prop (b /= bin_op op v1 v2) FF
                      _ -> it
    FF -> it

--------------------------------------------------------------------------------

class SignPP t where
  pp_neg :: Bool -> t -> Doc


instance SignPP RelOp where

  pp_neg False r = case r of
    Equal         -> text "=="
    LessThan      -> text "<"
    LessThanEqual -> text "<="

  pp_neg True r = case r of
    Equal         -> text "/="
    LessThan      -> text ">="
    LessThanEqual -> text ">"


pp_neg_div :: Bool -> Doc
pp_neg_div False  = text "|"
pp_neg_div True   = text "/|"


instance SignPP PosP where
  pp_neg n (Bin op t1 t2) = pp t1         <+> pp_neg n op  <+> pp t2
  pp_neg n (Divides d t)  = text (show d) <+> pp_neg_div n <+> pp t
  pp_neg n FF             = text (if n then "True" else "False")


instance SignPP VarP where
  pp_neg n (NBin op t)    = text "_" <+> pp_neg n op  <+> pp t
  pp_neg n (NDivides d t) = text (show d) <+> pp_neg_div n
                                          <+> text "_ +" <+> pp t


instance SignPP CVarP where
  pp_neg n p = case pprop p of
    NBin op t     -> it <+> pp_neg n op  <+> pp t
    NDivides d t  -> text (show d) <+> pp_neg_div n
                                   <+> it <+> text "+" <+> pp t
    where it  | c == 1    = text "_"
              | c == (-1) = text "- _"
              | otherwise = text (show c) <+> text "* _"

          c = coeff p 
               

instance SignPP p => PP (Prop p) where
  pp p  = pp_neg (negated p) (prop p)


instance SignPP p => PP (NormProp p) where
  pp (Ind p)  = pp p
  pp (Norm p) = pp p

