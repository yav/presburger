{-# LANGUAGE FlexibleInstances #-}

module Data.Integer.Presburger.HOAS
  ( Formula(..), check, translate
  , Quant, exists, forall
  , Term, (.*), is_constant
  , PP(..)
  ) where

import Data.Integer.Presburger.Form hiding (check)
import qualified Data.Integer.Presburger.Form as F

check :: Formula -> Bool
check f = F.check (translate f)


infixl 3 :/\:
infixl 2 :\/:
infixr 1 :=>:
infix  0 :<=>:

infix 4 :<:, :<=:, :>:, :>=:, :=:, :/=:, :|

-- Forst-oreder formulas for Presburger arithmetic.
data Formula  = Formula :/\: Formula
              | Formula :\/: Formula
              | Formula :=>: Formula
              | Formula :<=>: Formula
              | Not Formula
              | Exists (Term -> Formula)
              | Forall (Term -> Formula)
              | TRUE
              | FALSE
              | Term :<:   Term
              | Term :>:   Term
              | Term :<=:  Term
              | Term :>=:  Term
              | Term :=:   Term
              | Term :/=:  Term
              | Integer :| Term

translate :: Formula -> Form (Prop PosP)
translate = loop 0
  where loop n form = case form of
          Exists f    -> ex_step n (loop (n+1) (f (var n)))
          Forall f    -> loop n (Not (Exists (Not . f)))
          Not f       -> neg (loop n f)
          f1 :=>: f2  -> loop n (Not f1 :\/: f2)
          f1 :<=>: f2 -> loop n (f1 :/\: f2 :\/: Not f1 :/\: Not f2)
          f1 :/\: f2  -> Node And (loop n f1) (loop n f2)
          f1 :\/: f2  -> Node Or  (loop n f1) (loop n f2)
          
          FALSE       -> Leaf (Prop False FF)
          t1 :=: t2   -> Leaf (Prop False (Bin Equal t1 t2))
          t1 :<: t2   -> Leaf (Prop False (Bin LessThan t1 t2))
          t1 :<=: t2  -> Leaf (Prop False (Bin LessThanEqual t1 t2))

          TRUE        -> Leaf (Prop True FF)
          t1 :/=: t2  -> Leaf (Prop True (Bin Equal t1 t2))
          t1 :>=: t2  -> Leaf (Prop True (Bin LessThan t1 t2))
          t1 :>: t2   -> Leaf (Prop True (Bin LessThanEqual t1 t2))
            
          d :| t      -> Leaf (Prop False (Divides d t))

class Quant t where
  quant :: ((Term -> Formula) -> Formula) -> t -> Formula

instance Quant Formula where
  quant _ p = p

instance Quant t => Quant (Term -> t) where
  quant q p = q (\x -> quant q (p x))

exists, forall :: Quant t => t -> Formula
exists p  = quant Exists p
forall p  = quant Forall p

-- 4: wrap term, not
-- 3: wrap and
-- 2: wrap or
-- 1: wrap implies, quantifiers
instance PP Formula where
  pp = pp1 0 -- ' 0 0
    where
    pp1 :: Int -> Formula -> Doc
    pp1 p form = case form of
      _ :/\: _ -> hang (text "/\\") 2 (loop form)
        where loop (f1 :/\: f2) = loop f1 $$ loop f2
              loop f            = pp f

      _ :\/: _ -> hang (text "\\/") 2 (loop form)
        where loop (f1 :\/: f2) = loop f1 $$ loop f2
              loop f            = pp f

      _ -> pp' 0 p form



    pp' :: Int -> Name -> Formula -> Doc
    pp' n p form = case form of
      f1 :/\: f2 | n < 3  -> pp' 2 p f1 <+> text "/\\" <+> pp' 2 p f2
      f1 :\/: f2 | n < 2  -> pp' 1 p f1 <+> text "\\/" <+> pp' 1 p f2
      f1 :=>: f2 | n < 1  -> pp' 1 p f1 <+> text "=>" <+> pp' 0 p f2
      f1 :<=>: f2 | n < 1  -> pp' 1 p f1 <+> text "=>" <+> pp' 0 p f2
      Not f      | n < 4  -> text "Not" <+> pp' 4 p f
      Exists {}  | n < 1  -> pp_ex (text "exists") p form
        where pp_ex d q (Exists g) = pp_ex (d <+> text (var_name q))
                                                          (q+1) (g (var q))
              pp_ex d q g          = d <> text "." <+> pp' 0 q g

      Forall {} | n < 1 -> pp_ex (text "forall") p form
        where pp_ex d q (Forall g) = pp_ex (d <+> text (var_name q))
                                                          (q+1) (g (var q))
              pp_ex d q g          = d <> text "." <+> pp' 0 q g
      TRUE        -> text "true"
      FALSE       -> text "false"
      t1 :<:  t2 | n < 4  -> pp t1 <+> text "<"  <+> pp t2
      t1 :>:  t2 | n < 4  -> pp t1 <+> text ">"  <+> pp t2
      t1 :<=: t2 | n < 4  -> pp t1 <+> text "<=" <+> pp t2
      t1 :>=: t2 | n < 4  -> pp t1 <+> text ">=" <+> pp t2
      t1 :=:  t2 | n < 4  -> pp t1 <+> text "="  <+> pp t2
      t1 :/=: t2 | n < 4  -> pp t1 <+> text "/=" <+> pp t2
      k :| t1    | n < 4  -> text (show k) <+> text "|" <+> pp t1
      _ -> parens (pp' 0 p form)

