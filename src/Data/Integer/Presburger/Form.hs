module Data.Integer.Presburger.Form
  ( module Data.Integer.Presburger.Form
  , module Data.Integer.Presburger.Prop
  ) where

import Data.Integer.Presburger.Prop
import Data.Integer.Presburger.SolveDiv

check :: Form (Prop PosP) -> Bool
check f = eval_form f env_empty


data Conn       = And | Or deriving Eq
data Form p     = Node !Conn (Form p) (Form p)
                | Leaf !p

                -- A special form of disjunction. Bool = negated?
                | Ex Bool (Name,Integer) (Form p)

instance Functor Form where
  fmap f (Node c f1 f2)    = Node c (fmap f f1) (fmap f f2)
  fmap f (Ex b xs g)       = Ex b xs (fmap f g)
  fmap f (Leaf p)          = Leaf (f p)

form_lcm                  :: Form (NormProp CVarP) -> Integer
form_lcm (Node _ f1 f2)    = lcm (form_lcm f1) (form_lcm f2)
form_lcm (Leaf p)          = case p of
                               Ind {}  -> 1
                               Norm p1 -> coeff (prop p1)
form_lcm (Ex _ _ f)        = form_lcm f



form_scale  :: Name -> Form (Prop PosP) -> Form (NormProp VarP)
form_scale x form
  | k /= 1    = Node And (Leaf $ Norm $ Prop False $ NDivides k 0) sf
  | otherwise = sf
  where
  nf  = fmap (norm x) form
  k   = form_lcm nf
  sf  = fmap leaf nf

  leaf p = case p of
             Ind p1  -> Ind p1
             Norm p1 -> Norm (scale k p1)


-- The integer is "length as - length bs"
a_b_sets :: (Integer,[Term],[Term]) -> NormProp VarP -> (Integer,[Term],[Term])
a_b_sets (o,as,bs) p = case p of
  Ind _                       -> (o,as,bs)
  Norm (Prop _ (NDivides {})) -> (o,as,bs)

  -- positive
  Norm (Prop False (NBin op t)) ->
    case op of
      LessThan      -> (1 + o , t     : as,         bs)
      LessThanEqual -> (1 + o , (t+1) : as,         bs)
      Equal         -> (o     , (t+1) : as, (t-1) : bs)

  -- negative
  Norm (Prop True (NBin op t)) ->
    case op of
      LessThan      -> (o - 1 ,         as, (t-1) : bs)
      LessThanEqual -> (o - 1 ,         as, t     : bs)
      Equal         -> (o     , t     : as, t     : bs)


form_pos_inf :: Term -> Form (NormProp VarP) -> Form (Prop PosP)
form_pos_inf t form = fmap leaf form
  where leaf p = case p of
                   Ind p1  -> p1
                   Norm p1 -> pos_inf t p1

form_neg_inf :: Term -> Form (NormProp VarP) -> Form (Prop PosP)
form_neg_inf t form = fmap leaf form
  where leaf p  = case p of
                    Ind p1  -> p1
                    Norm p1 -> neg_inf t p1

form_no_inf :: Term -> Form (NormProp VarP) -> Form (Prop PosP)
form_no_inf t form  = fmap leaf form
  where leaf p  = case p of
                    Ind p1  -> p1
                    Norm p1 -> normal t p1


neg :: Form (Prop PosP) -> Form (Prop PosP)
neg (Node And f1 f2)  = Node Or (neg f1) (neg f2)
neg (Node Or f1 f2)   = Node And (neg f1) (neg f2)
neg (Ex b x f)        = Ex (not b) x f
neg (Leaf (Prop b p)) = Leaf (Prop (not b) p)


simplify :: Form (Prop PosP) -> Form (Prop PosP)
simplify (Node c f1 f2) =
  case simplify f1 of
    r@(Leaf (Prop n FF)) | n && c == Or
                        || not n && c == And -> r
                         | otherwise -> simplify f2
    r1 -> case simplify f2 of
            r@(Leaf (Prop n FF)) | n && c == Or
                                || not n && c == And -> r
                                 | otherwise -> r1
            r2 -> Node c r1 r2



simplify (Ex False (x,1) f) = simplify (subst_form x 1 f)
simplify (Ex True (x,1) f)  = simplify (neg (subst_form x 1 f))

simplify (Ex b x f) = case simplify f of
                        Leaf (Prop n FF) -> Leaf (Prop (not (b == n)) FF)
                        f1               -> Ex b x f1
                              
simplify (Leaf l) = Leaf (simplify_prop l)



ex_step :: Name -> Form (Prop PosP) -> Form (Prop PosP)
ex_step x (Node Or f1 f2) = Node Or (ex_step x f1) (ex_step x f2)
ex_step x f
  | as_minus_bs >= 0    = thm_as as x norm_f
  | otherwise           = thm_bs bs x norm_f
  
  where 
  norm_f               :: Form (NormProp VarP)
  norm_f                = form_scale x f

  (as_minus_bs, as, bs) = loop (0,[],[]) norm_f

  loop s (Node _ f1 f2) = loop (loop s f1) f2
  loop s (Ex _ _ f1)    = loop s f1
  loop s (Leaf p)       = a_b_sets s p



thm_as :: [Term] -> Name -> Form (NormProp VarP) -> Form (Prop PosP)
thm_as as x f = simplify $
  foldr1 (Node Or) $ map (Ex False (x, form_bound f))
                   $ form_pos_inf (negate (var x)) f
                   : [ form_no_inf (a - var x) f | a <- as ]

thm_bs :: [Term] -> Name -> Form (NormProp VarP) -> Form (Prop PosP)
thm_bs bs x f = simplify $
  foldr1 (Node Or) $ map (Ex False (x, form_bound f))
                   $ form_neg_inf (var x) f
                   : [ form_no_inf (b + var x) f | b <- bs ]


form_bound                :: Form (NormProp VarP) -> Integer
form_bound (Node _ f1 f2)  = lcm (form_bound f1) (form_bound f2)
form_bound (Leaf p)        = case p of
                               Norm (Prop _ (NDivides n _)) -> n
                               _ -> 1
form_bound (Ex _ _ f)      = form_bound f


-- Evaluation ------------------------------------------------------------------

-- The meanings of formulas.
eval_form :: Form (Prop PosP) -> Env -> Bool
eval_form (Node c p q) env  = eval_conn c (eval_form p env) (eval_form q env)
eval_form (Leaf p) env      = eval_prop p env
eval_form (Ex b x f) env0   = case splt f [x] of
                                (xs,cs,f1) -> let v = any (eval_form f1) (elim env0 xs cs)
                                              in if b then not v else v
  where splt (Ex False y f1) ys = splt f1 (y:ys)
        splt f1 ys          = case split_divs f1 of
                                 (ds,f2) -> (ys,ds,f2)



split_ands :: Form p -> [Form p]
split_ands form = loop form []
  where loop (Node And f1 f2) fs  = loop f1 (loop f2 fs)
        loop f fs                 = f : fs

split_divs :: Form (Prop PosP) -> ([DivCtr], Form (Prop PosP))
split_divs form = loop (split_ands form) ([], Leaf (Prop True FF))
  where
  loop (Leaf (Prop False (Divides n t)) : fs) (cs, f)
                              = loop fs (Divs n t : cs, f)
  loop (f:fs) (cs, f1)        = loop fs (cs, Node And f f1)
  loop [] cs                  = cs


-- The meanings of connectives.
eval_conn :: Conn -> Bool -> Bool -> Bool
eval_conn And = (&&)
eval_conn Or  = (||)

subst_form :: Name -> Integer -> Form (Prop PosP) -> Form (Prop PosP)
subst_form x n f = fmap (subst_prop x n) f
--------------------------------------------------------------------------------

instance PP Conn where
  pp And  = text "/\\"
  pp Or   = text "\\/"

instance PP p => PP (Form p) where
  pp me@(Node c _ _) = hang (pp c) 2 (vcat $ map pp $ jn me [])
    where jn (Node c1 p1 q1) fs | c == c1 = jn p1 (jn q1 fs)
          jn f fs = f : fs
  pp (Leaf p)     = pp p

  pp (Ex n q f) = hang (how <+> quant q <> text ".") 2 (pp f)
    where quant (x,b) = text (var_name x) <+> text "<=" <+> text (show b)
          how = (if n then text "Not" else empty) <+> text "Ex"




