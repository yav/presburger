module Data.Integer.Presburger.ModArith where

import Data.Integer.Presburger

is_nat         :: Term -> Formula
is_nat t        = 0 :<=: t

is_reminder    :: Integer -> Term -> Formula
is_reminder d r = is_nat r :/\: r :<: fromIntegral d

-- | divMod t d == (q,r)
div_mod_is     :: Term -> Integer -> Term -> Term -> Formula
div_mod_is t d q r = is_reminder d r :/\: d .* q + r :=: t

-- | mod t d == r
mod_is         :: Term -> Integer -> Term -> Formula
mod_is t d r    = is_reminder d r :/\: d :| (t - r)

bin_op_mod :: Integer -> (Term -> Term -> Term)
           -> Term -> Term -> Term -> Formula
bin_op_mod d f t1 t2 t3 = mod_is (f t1 t2) d t3

add_mod, sub_mod, mul_mod :: Integer -> Term -> Term -> Term -> Formula
add_mod d = bin_op_mod d (+)
sub_mod d = bin_op_mod d (-)
mul_mod d = bin_op_mod d (*)




