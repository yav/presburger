{-| This module implements Cooper's algorithm for deciding
    first order formulas over integers with addition.

Based on the paper:
  author: D.C.Cooper
  title:  "Theorem Proving in Arithmetic without Multiplication"
  year:   1972
-}
module Presburger
  ( check

  , Term
  , num
  , (.+.), (.+), (+.)
  , (.-.), (.-), (-.)
  , (.*), (*.)
  , neg

  , Formula
  , false, ors, (\/)
  , true, ands, (/\)
  , (==>)
  , not_
  , (.<.), (.<=.), (.>.), (.>=.)
  , (.=.), (./=.)
  , (|.)
  , forall, exists
  , forall_nat, exists_nat
  ) where

import qualified Data.IntMap as Map
import Data.Maybe
import Data.List

import Text.PrettyPrint.HughesPJ


-- | Decide the validity of a formula.
check              :: Formula -> Bool
check (F f)         = eval_form (f 0)


-- Terms ----------------------------------------------------------------------

-- | Integer terms.
data Term = Term (Map.IntMap Integer) Integer

class PP a where
  pp :: a -> Doc

instance PP Term where
  pp (Term m k) | isEmpty vars  = text (show k)
                | k == 0        = vars
                | k > 0         = vars <+> char '+' <+> text (show k)
                | otherwise     = vars <+> char '-' <+> text (show $ abs k)
    where var (x,n) = sign <+> co <+> text (var_name x)
            where (sign,co)
                     | n < 0      = (char '-', text (show (abs n)) <+> char '*')
                     | n == 1     = (char '+', empty)
                     | otherwise  = (char '+', text (show n) <+> char '*')
          first_var (x,n) = text (show n) <+> char '*' <+> text (var_name x)

          vars = case filter ((/= 0) . snd) (Map.toList m) of
                   []     -> empty
                   v : vs -> first_var v <+> hsep (map var vs)


var_name :: Name -> String
var_name x = let (a,b) = divMod x 26
                 rest = if a == 0 then "" else show a
             in toEnum (97 + b) : rest

-- | Integer constant.
num                :: Integer -> Term
num x               = Term Map.empty (fromIntegral x)

infixl 6 .+.
-- | The sum of two terms.
(.+.)              :: Term -> Term -> Term
Term m1 n1 .+. Term m2 n2 = Term (Map.unionWith (+) m1 m2) (n1 + n2)

infixl 6 .+
-- | Increment a term by an integer.
(.+)               :: Term -> Integer -> Term
Term m n .+ k       = Term m (n + k)

infixr 6 +.
-- | Increment a term by an integer.
(+.)               :: Integer -> Term -> Term
k +. t              = t .+ k

infixr 7 *.
-- | Multiply a term by an integer constant.
(*.)               :: Integer -> Term -> Term
0 *. _              = num 0
1 *. t              = t
k *. Term m n       = Term (Map.map (k *) m) (k * n)

infixl 7 .*
-- | Multiply a term by an integer constant.
(.*)               :: Term -> Integer -> Term
t .* k              = k *. t

-- | Negate a term.
neg                :: Term -> Term
neg (Term m n)      = Term (Map.map negate m) (negate n)

infixl 6 .-.
-- | Subtract two terms.
(.-.)              :: Term -> Term -> Term
Term m1 n1 .-. Term m2 n2 = Term (Map.unionWith subtract m1 m2) (n1 - n2)

infixl 6 .-
-- | Decrement a term by an integer.
(.-)               :: Term -> Integer -> Term
Term m n .- k       = Term m (n - k)

infixl 6 -.
-- | Subtract a term from an integer.
(-.)               :: Integer -> Term -> Term
k -. Term m n       = Term (Map.map negate m) (k - n)



-- Formulas --------------------------------------------------------------------

-- | First order formulas.
newtype Formula     = F (Int -> Form Pred)

-- | False formula.
false              :: Formula
false               = lift (Or [])

-- | True formula.
true               :: Formula
true                = lift (And [])

-- | The disjunction of a list of formulas.
ors                :: [Formula] -> Formula
ors fs              = F (\x -> Or [ f x | F f <- fs ])

-- | The conjunction of a list of formulas.
ands               :: [Formula] -> Formula
ands fs             = F (\x -> And [ f x | F f <- fs])

infixl 3 /\
-- | The conjunction of two formulas.
(/\)               :: Formula -> Formula -> Formula
F p /\ F q          = F (\x -> And [ p x, q x ])

infixl 2 \/
-- | The disjunction of two formulas.
(\/)               :: Formula -> Formula -> Formula
F p \/ F q          = F (\x -> Or [ p x, q x ])

infixr 1 ==>
-- | Implication.
(==>)              :: Formula -> Formula -> Formula
p ==> q             = not_ p \/ q

-- | Negation.
not_               :: Formula -> Formula
not_ (F p)          = F (\x -> not' (p x))

infix 4 .<.
-- | Check if one term is strictly smaller then another.
(.<.)              :: Term -> Term -> Formula
t1 .<. t2           = lift $ Pred (Op2 LessThen t1 t2)

infix 4 .<=.
-- | Check if one term is smaller then, or equal to another.
(.<=.)             :: Term -> Term -> Formula
t1 .<=. t2          = lift $ Pred (Op2 LessThenEqual t1 t2)

infix 4 .>.
-- | Check if one term is strictly greater then another.
(.>.)              :: Term -> Term -> Formula
t1 .>. t2           = not_ (t1 .<=. t2)

infix 4 .>=.
-- | Check if one term is greater-then, or equal to another.
(.>=.)             :: Term -> Term -> Formula
t1 .>=. t2          = not_ (t1 .<. t2)

infix 4 .=.
-- | Check if two terms are equal.
(.=.)              :: Term -> Term -> Formula
t1 .=. t2           = lift $ Pred $ Op2 Equal t1 t2

infix 4 ./=.
-- | Check if two terms are not equal.
(./=.)             :: Term -> Term -> Formula
t1 ./=. t2          = lift $ Pred $ Op2 NotEqual t1 t2

-- | Check if a term is divisible by an integer constant.
(|.)               :: Integer -> Term -> Formula
1 |. _              = true
k |. t              = lift $ Pred $ Op1 (Divides k) t

-- | Check for the existance of an integer that satisfies the formula.
exists             :: (Term -> Formula) -> Formula
exists f            = F (\x -> let F g = f (Term (Map.singleton x 1) 0)
                               in exists' x (g (x+1)))

-- | Check if all integers satisfy the formula.
forall             :: (Term -> Formula) -> Formula
forall t            = not_ $ exists $ \x -> not_ (t x)

-- | Check for the existance of a natural number that satisfies the formula.
exists_nat         :: (Term -> Formula) -> Formula
exists_nat f        = exists $ \x -> x .>=. num 0 /\ f x

-- | Check if all natural numbers satisfy the formula.
forall_nat         :: (Term -> Formula) -> Formula
forall_nat f        = not_ $ exists_nat $ \x -> not_ (f x)


--------------------------------------------------------------------------------

lift               :: Form Pred -> Formula
lift p              = F (\_ -> p)

type Name           = Int

coeff              :: Name -> Term -> Integer
coeff x (Term m _)  = fromMaybe 0 (Map.lookup x m)

constant           :: Term -> Integer
constant (Term _ k) = k

rm_var             :: Name -> Term -> Term
rm_var x (Term m k) = Term (Map.delete x m) k

data Op1        = Divides Integer | NotDivides Integer
data Op2        = LessThen | LessThenEqual | Equal | NotEqual

data Pred       = Op1 !Op1 Term
                | Op2 !Op2 Term Term

data VarPred    = VOp1 !Op1 Term
                | VOp2 !Op2 Term
                | GreaterThen Term
                | GreaterThenEqual Term
                | Independent Pred

data Form p     = And  [Form p]
                | Or   [Form p]
                | Pred p

instance PP Pred where
  pp (Op2 op t1 t2) = pp t1 <+> pp op <+> pp t2
  pp (Op1 op t1)    = pp op <+> pp t1

instance PP Op1 where
  pp (Divides x)    = text (show x) <+> char '|'
  pp (NotDivides x) = text (show x) <+> text "/|"

instance PP Op2 where
  pp LessThen       = text "<"
  pp LessThenEqual  = text "<="
  pp Equal          = text "="
  pp NotEqual       = text "/="

instance PP p => PP (Form p) where
  pp f = case f of
    And []  -> text "True"
    And fs  -> hang (text "AND") 2 (vcat $ map pp fs)
    Or []   -> text "False"
    Or fs   -> hang (text "OR") 2 (vcat $ map pp fs)
    Pred p  -> pp p

instance PP Formula where
  pp (F f)  = pp (f 0)


not' :: Form Pred -> Form Pred
not' t = case t of
  And ts  -> Or (map not' ts)
  Or ts   -> And (map not' ts)
  Pred p -> Pred $ case p of
    Op2 op t1 t2 -> case op of
      LessThen      -> Op2 LessThenEqual t2 t1
      LessThenEqual -> Op2 LessThen t2 t1
      Equal         -> Op2 NotEqual t1 t2
      NotEqual      -> Op2 Equal t1 t2
    Op1 op t1 -> case op of
      Divides k     -> Op1 (NotDivides k) t1
      NotDivides k  -> Op1 (Divides k) t1

tt :: Form p
tt = And []

ff :: Form p
ff = Or []




other_op :: Op2 -> Term -> VarPred
other_op op = case op of
  LessThen      -> GreaterThen
  LessThenEqual -> GreaterThenEqual
  Equal         -> VOp2 Equal
  NotEqual      -> VOp2 NotEqual

norm :: Name -> Integer -> Pred -> (Integer, VarPred)
norm x n (Op2 op t1 t2)
  | k1 == k2  = (1, Independent $ Op2 op t1' t2')
  | k1 > k2   = scale n (k1 - k2) (VOp2 op)     (t2' .-. t1')
  | otherwise = scale n (k2 - k1) (other_op op) (t1' .-. t2')

  where t1' = rm_var x t1
        t2' = rm_var x t2

        k1  = coeff x t1
        k2  = coeff x t2


norm x n p@(Op1 op t)
  | k == 0    = (1, Independent p)
  | k > 0     = scale n k          (scaled_op k) t'
  | otherwise = scale n (negate k) (scaled_op (negate k)) (neg t')
  where t' = rm_var x t
        k  = coeff x t

        scaled_op k' = case op of
                         Divides d     -> VOp1 $ Divides    $ d * (n `div` k')
                         NotDivides d  -> VOp1 $ NotDivides $ d * (n `div` k')

scale :: Integer -> Integer -> (Term -> VarPred) -> Term -> (Integer, VarPred)
scale n k f t = (k, f ((n `div` k) *. t))


-- NOTE: When equal use one with fewer variables?
exists' :: Name -> Form Pred -> Form Pred
exists' x t = let (t1,d,as,bs) = analyze x t
              in if longer_or_equal as bs
                    then ver_b d t1 bs
                    else ver_a d t1 as

  where
  ver_a d t1 as =
    Or ( [ body x pos_inf (num (negate j)) t1 | j <- [1 .. d] ]
      ++ [ body x normal  (a .- j) t1         | j <- [1 .. d], a <- as ]
       )

  ver_b d t1 bs =
    Or ( [ body x neg_inf (num j) t1 | j <- [1 .. d] ]
      ++ [ body x normal (b .+ j) t1 | j <- [1 .. d ], b <- bs ]
       )




analyze :: Name -> Form Pred
        -> ( Form VarPred     -- Normalized formula
           , Integer          -- delta
           , [Term]           -- A set
           , [Term]           -- B set
           )


analyze x term = ( And [t1, Pred $ VOp1 (Divides final_k) (num 0)]
                 , d1, as1, bs1)

  where (t1, final_k, d1, as1, bs1) = loop term

        loop f = case f of
          And ts -> let (fs,ks,ds,as,bs) = unzip5 (map loop ts)
                    in (And fs, lcms ks, lcms ds, concat as, concat bs)

          Or ts  -> let (fs,ks,ds,as,bs) = unzip5 (map loop ts)
                    in (Or fs, lcms ks, lcms ds, concat as, concat bs)

          Pred p ->
            let (k,f1) = norm x final_k p
                (d, as, bs) = case f1 of
                   VOp2 op t -> case op of
                     LessThen         -> (1, [t], [])
                     LessThenEqual    -> (1, [t .+ 1], [])
                     Equal            -> (1, [t .+ 1], [t .- 1])
                     NotEqual         -> (1, [t],[t])

                   GreaterThen t      -> (1, [], [t])
                   GreaterThenEqual t -> (1, [], [t .- 1])
                   VOp1 op _          -> (d2, [], [])
                     where d2 = case op of
                                  Divides delta    -> delta
                                  NotDivides delta -> delta
                   Independent {}     -> (1, [], [])
            in (Pred f1, k, d, as, bs)




-- Special cases for the body of an existential --------------------------------

body :: Name -> (VarPred -> Term -> Form Pred) -> Term -> Form VarPred
      -> Form Pred
body v how x t = case t of
  Pred p -> how p x
  And fs -> And (map (body v how x) fs)
  Or fs  -> Or (map (body v how x) fs)

normal :: VarPred -> Term -> Form Pred
normal p t = Pred $ case p of
  VOp2 op t1          -> Op2 op t t1
  GreaterThen t1      -> Op2 LessThen t1 t
  GreaterThenEqual t1 -> Op2 LessThenEqual t1 t
  VOp1 op t1          -> Op1 op (t .+. t1)
  Independent p1      -> p1

neg_inf :: VarPred -> Term -> Form Pred
neg_inf p t = case p of
  VOp2 op _           -> case op of
    LessThen          -> tt
    LessThenEqual     -> tt
    Equal             -> ff
    NotEqual          -> tt
  GreaterThen {}      -> ff
  GreaterThenEqual {} -> ff
  VOp1 op t1          -> Pred (Op1 op (t .+. t1)) -- depends on var.
  Independent p1      -> Pred p1

pos_inf :: VarPred -> Term -> Form Pred
pos_inf p t = case p of
  VOp2 op _           -> case op of
    LessThen          -> ff
    LessThenEqual     -> ff
    Equal             -> ff
    NotEqual          -> tt
  GreaterThen {}      -> tt
  GreaterThenEqual {} -> tt
  VOp1 op t1          -> Pred (Op1 op (t .+. t1)) -- depends on var.
  Independent p1      -> Pred p1



-- Evaluation ------------------------------------------------------------------

eval_form :: Form Pred -> Bool
eval_form f = case f of
  And fs        -> and (map eval_form fs)
  Or fs         -> or (map eval_form fs)
  Pred p        -> eval_pred p

eval_pred :: Pred -> Bool
eval_pred p = case p of
  Op2 op t1 t2  -> eval_op2 op (eval_term t1) (eval_term t2)
  Op1 op t1     -> eval_op1 op (eval_term t1)

eval_op2 :: Op2 -> Integer -> Integer -> Bool
eval_op2 op = case op of
  LessThen      -> (<)
  LessThenEqual -> (<=)
  Equal         -> (==)
  NotEqual      -> (/=)

eval_op1 :: Op1 -> Integer -> Bool
eval_op1 op x = case op of
  Divides k     -> (x `mod` k) == 0
  NotDivides k  -> (x `mod` k) /= 0

eval_term :: Term -> Integer
eval_term t = constant t -- should be no varibales


--------------------------------------------------------------------------------



-- Misc -----------------------------------------------------------------------

lcms :: [Integer] -> Integer
lcms xs = foldr lcm 1 xs

longer_or_equal :: [a] -> [a] -> Bool
longer_or_equal (_:xs) (_:ys) = longer_or_equal xs ys
longer_or_equal [] (_:_)      = False
longer_or_equal _ _           = True



