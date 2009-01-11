{-# LANGUAGE FlexibleInstances #-}

{-| This module implements Cooper's algorithm for deciding
    first order formulas over integers with addition.

Based on the paper:
  author: D.C.Cooper
  title:  "Theorem Proving in Arithmetic without Multiplication"
  year:   1972
-}
module Presburger where

import qualified Data.IntMap as Map
import Data.Maybe
import Data.List
import Control.Monad(mplus,guard)
import Prelude hiding (LT,EQ)

import Text.PrettyPrint.HughesPJ
import Debug.Trace

check :: Formula -> Bool
check (F f) = eval_form (f 0)

-- Sugar -----------------------------------------------------------------------

-- | First order formulas.
newtype Formula     = F (Int -> Form)

instance PP Formula where
  pp (F f) = pp (f 0)

instance Show Formula where show = show . pp

-- | False formula.
false              :: Formula
false               = lift ff'

-- | True formula.
true               :: Formula
true                = not_ false

infixl 3 /\
-- | The conjunction of two formulas.
(/\)               :: Formula -> Formula -> Formula
F p /\ F q          = F (\x -> and' (p x) (q x))

infixl 2 \/
-- | The disjunction of two formulas.
(\/)               :: Formula -> Formula -> Formula
F p \/ F q          = F (\x -> or' (p x) (q x))

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
t1 .<. t2           = lift $ Prop $ Pred LT True :> [t1,t2]

infix 4 .<=.
-- | Check if one term is smaller then, or equal to another.
(.<=.)             :: Term -> Term -> Formula
t1 .<=. t2          = lift $ Prop $ Pred LEQ True :> [t1,t2]

infix 4 .>.
-- | Check if one term is strictly greater then another.
(.>.)              :: Term -> Term -> Formula
t1 .>. t2           = t2 .<. t1

infix 4 .>=.
-- | Check if one term is greater-then, or equal to another.
(.>=.)             :: Term -> Term -> Formula
t1 .>=. t2          = t2 .<=. t1

infix 4 ===
-- | Check if two terms are equal.
(===)              :: Term -> Term -> Formula
t1 === t2           = lift $ Prop $ Pred EQ True :> [t1,t2]

infix 4 =/=
-- | Check if two terms are not equal.
(=/=)              :: Term -> Term -> Formula
t1 =/= t2           = lift $ Prop $ Pred EQ False :> [t1,t2]

-- | Check if a term is divisible by an integer constant.
(|.)               :: Integer -> Term -> Formula
1 |. _              = true
k |. t              = lift $ Prop $ Pred (Divs k) True :> [t]


class Exists a where
  exists' :: [Name] -> (Term -> a) -> Formula

instance Exists Formula where
  exists' xs f = F (\x -> let F g = f (var x) in exists_many (x:xs) (g (x+1)))

instance Exists t => Exists (Term -> t) where
  exists' xs f = F $ \x -> let F g = exists' (x:xs) (f (var x)) in g (x+1)

-- | Check for the existance of an integer that satisfies the formula.
exists             :: Exists t => (Term -> t) -> Formula
exists f            = exists' [] f

{-
-- | Check for the existance of an integer that satisfies the formula.
exists             :: (Term -> Formula) -> Formula
-- | Check if all integers satisfy the formula.
forall             :: ([Term] -> Formula) -> Formula
forall t            = not_ $ exists $ \x -> not_ (t x)

-- | Check for the existance of a natural number that satisfies the formula.
exists_nat         :: (Term -> Formula) -> Formula
exists_nat f        = exists $ \x -> x .>=. 0 /\ f x

-- | Check if all natural numbers satisfy the formula.
forall_nat         :: (Term -> Formula) -> Formula
forall_nat f        = not_ $ exists_nat $ \x -> not_ (f x)
-}

lift :: Form -> Formula
lift p = F (\_ -> p)

-- Terms ----------------------------------------------------------------------

-- | Integer terms.
data Term = Term (Map.IntMap Integer) Integer



type Name           = Int

var_name           :: Name -> String
var_name x          = let (a,b) = divMod x 26
                          rest = if a == 0 then "" else show a
                      in toEnum (97 + b) : rest

coeff              :: Name -> Term -> Integer
coeff x (Term m _)  = fromMaybe 0 (Map.lookup x m)

rm_var             :: Name -> Term -> Term
rm_var x (Term m k) = Term (Map.delete x m) k

var                :: Name -> Term
var x               = Term (Map.singleton x 1) 0

num                :: Integer -> Term
num n               = Term Map.empty n





class PP a where
  pp :: a -> Doc

instance PP Term where
  pp (Term m k) | isEmpty vars  = text (show k)
                | k == 0        = vars
                | k > 0         = vars <+> char '+' <+> text (show k)
                | otherwise     = vars <+> char '-' <+> text (show $ abs k)
    where ppvar (x,n) = sign <+> co <+> text (var_name x)
            where (sign,co)
                     | n == -1    = (char '-', empty)
                     | n < 0      = (char '-', text (show (abs n)) <+> char '*')
                     | n == 1     = (char '+', empty)
                     | otherwise  = (char '+', text (show n) <+> char '*')
          first_var (x,1)  = text (var_name x)
          first_var (x,-1) = char '-' <> text (var_name x)
          first_var (x,n)  = text (show n) <+> char '*' <+> text (var_name x)

          vars = case filter ((/= 0) . snd) (Map.toList m) of
                   []     -> empty
                   v : vs -> first_var v <+> hsep (map ppvar vs)

instance Show Term where
  show x = show (pp x)

instance Eq Term where
  t1 == t2  = is_constant (t1 - t2) == Just 0

instance Num Term where
  fromInteger n             = Term Map.empty n
  Term m1 n1 + Term m2 n2   = Term (Map.unionWith (+) m1 m2) (n1 + n2)
  negate (Term m n)         = Term (Map.map negate m) (negate n)
  t1 * t2  = case fmap (.* t2) (is_constant t1) `mplus`
                  fmap (.* t1) (is_constant t2) of
               Just t  -> t
               Nothing -> error $ unlines [ "[(*) @ Term] Non-linear product:"
                                          , "  *** " ++ show t1
                                          , "  *** " ++ show t2
                                          ]
  signum t  = case is_constant t of
                Just n  -> num (signum n)
                Nothing -> error $ unlines [ "[signum @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]

  abs t   = case is_constant t of
                Just n  -> num (abs n)
                Nothing -> error $ unlines [ "[abs @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]
  

-- | Check if a term is a constant (i.e., contains no variables).
-- If so, then we return the constant, otherwise we return 'Nothing'.
is_constant :: Term -> Maybe Integer
is_constant (Term m n) = guard (all (0 ==) (Map.elems m)) >> return n

(.*) :: Integer -> Term -> Term
0 .* _        = 0
1 .* t        = t
k .* Term m n = Term (Map.map (k *) m) (k * n)


-- Propositions ----------------------------------------------------------------

data PredSym    = FF | LT | LEQ | EQ | Divs Integer {- +ve -}
data Pred       = Pred PredSym Bool -- Bool: positive (i.e. non-negated)?
data Prop       = Pred :> [Term]    
data Conn       = And | Or deriving Eq
data Form       = Conn Conn Form Form | Prop Prop

abs_form       :: Form -> ([Prop],[Prop] -> Form)
abs_form fo     = let (ps,skel) = loop [] fo
                  in (reverse ps, fst . skel)
  where loop ps (Conn c p q) =
          let (ps1,f1) = loop ps p
              (ps2,f2) = loop ps1 q
          in (ps2, \fs -> let (p1,fs1) = f1 fs
                              (p2,fs2) = f2 fs1
                          in (Conn c p1 p2, fs2))
        loop ps (Prop p) = (p:ps, \(f:fs) -> (Prop f,fs))


instance PP PredSym where
  pp p = case p of
    FF      -> text "false"
    LT      -> text "<"
    LEQ     -> text "<="
    EQ      -> text "==="
    Divs n  -> text (show n) <+> text "|"

instance PP Pred where
  pp (Pred p True) = pp p
  pp (Pred p False) = case p of
    FF      -> text "true"
    LT      -> text ">="
    LEQ     -> text ">"
    EQ      -> text "=/="
    Divs n  -> text (show n) <+> text "/|"

instance PP Prop where
  pp (p :> [t1,t2]) = pp t1 <+> pp p <+> pp t2
  pp (p :> ts)      = pp p <+> hsep (map pp ts)

instance Show Prop where show = show . pp

instance PP Conn where
  pp And  = text "/\\"
  pp Or   = text "\\/"

instance PP Form where
  pp me@(Conn c _ _) = hang (pp c) 2 (vcat $ map pp $ jn me [])
    where jn (Conn c1 p1 q1) fs | c == c1 = jn p1 (jn q1 fs)
          jn f fs = f : fs
  pp (Prop p)     = pp p

not' :: Form -> Form
not' (Conn c t1 t2) = Conn (not_conn c) (not' t1) (not' t2)
not' (Prop p)       = Prop (not_prop p)

ff' :: Form
ff' = Prop $ Pred FF True :>[]

and' :: Form -> Form -> Form
and' p q = Conn And p q

or' :: Form -> Form -> Form
or' p q = Conn Or p q

ors' :: [Form] -> Form
ors' [] = ff'
ors' xs = foldr1 or' xs



not_conn :: Conn -> Conn
not_conn And = Or
not_conn Or  = And

not_prop :: Prop -> Prop
not_prop (f :> ts) = not_pred f :> ts

not_pred :: Pred -> Pred
not_pred (Pred p pos) = Pred p (not pos)


data NormProp = Ind Prop
              | L Pred Term

instance PP NormProp where
  pp (Ind p)  = pp p
  pp (L p@(Pred (Divs {}) _) t) = pp p <+> text "_ +" <+> pp t
  pp (L p t)                    = text "_" <+> pp p <+> pp t

instance Show NormProp where show = show . pp

norm2 :: Name -> Integer -> Pred -> Term -> Term -> (Integer,NormProp)
norm2 x final_k p t1 t2
  | k1 == k2   = (1, Ind (p :> [t1',t2']))
  | k1 > k2    = (abs k, L p t)
  | otherwise  = (abs k, L p' t)

  where t1' = rm_var x t1
        t2' = rm_var x t2

        k1  = coeff x t1
        k2  = coeff x t2

        k   = k1 - k2
        t   = (final_k `div` k) .* (t2' - t1')   -- only used when k /= 0
       
        p'  = case p of
                Pred LT b  -> Pred LEQ (not b)
                Pred LEQ b -> Pred LT (not b)
                _          -> p
  
norm1 :: Name -> Integer -> Pred -> Term -> (Integer,NormProp)
norm1 x final_k p@(Pred (Divs d) b) t
  | k == 0    = (1, Ind (p :> [t]))
  | otherwise = (abs k, L ps (l .* t'))

  where t'  = rm_var x t
        k   = coeff x t

        l   = final_k `div` k
        ps  = Pred (Divs (d * abs l)) b

norm1 _ _ _ _ = error "(bug) norm1 applied to a non-unary operator"


norm_prop :: Name -> Integer -> Prop -> (Integer,NormProp)
norm_prop _ _ p@(_ :> [])           = (1,Ind p)
norm_prop x final_k (p :> [t])      = norm1 x final_k p t
norm_prop x final_k (p :> [t1,t2])  = norm2 x final_k p t1 t2
norm_prop _ _ _                     = error "(bug) norm_prop on arity > 2"

norm_props :: Name -> [Prop] -> (Integer,[NormProp])
norm_props x ps = (final_k, ps1)
  where (ks,ps1) = unzip $ map (norm_prop x final_k) ps
        final_k  = lcms ks

a_b_sets :: ([Term],[Term]) -> NormProp -> ([Term],[Term])
a_b_sets (as,bs) p = case p of
  Ind _ -> (as,bs)

  L (Pred op True) t ->
    case op of
      LT  -> (t     : as,           bs)
      LEQ -> ((t+1) : as,           bs)
      EQ  -> ((t+1) : as, (t - 1) : bs)
      _   -> (        as,           bs)

  L (Pred op False) t ->
    case op of
      LT  -> (        as, (t-1)   : bs)
      LEQ -> (        as, t       : bs)
      EQ  -> (t     : as, t       : bs)
      _   -> (        as,           bs)


analyze_props :: Name -> [Prop] -> ( [NormProp]
                                   , Integer    -- scale
                                   , Integer    -- bound
                                   , [Term]     -- A set
                                   , [Term]     -- B set
                                   )
analyze_props x ps = (ps1, final_k, bnd, as, bs)
  where (ks,ps1)  = unzip $ map (norm_prop x final_k) ps
        final_k   = lcms ks
        (as,bs)   = foldl' a_b_sets ([],[]) ps1
        bnd       = lcms (final_k : [ d | L (Pred (Divs d) _) _ <- ps1 ])

from_bool :: Bool -> Prop
from_bool True  = Pred FF False :> []
from_bool False = Pred FF True :> []

neg_inf :: NormProp -> Term -> Prop
neg_inf prop t = case prop of
  Ind p -> p
  L ps@(Pred op pos) t1 -> case op of
    LT      -> from_bool pos
    LEQ     -> from_bool pos
    EQ      -> from_bool (not pos)
    Divs {} -> ps :> [t + t1]
    FF      -> error "(bug) FF in NormPred"

pos_inf :: NormProp -> Term -> Prop
pos_inf prop t = case prop of
  Ind p -> p
  L ps@(Pred op pos) t1 -> case op of
    LT      -> from_bool (not pos)
    LEQ     -> from_bool (not pos)
    EQ      -> from_bool (not pos)
    Divs {} -> ps :> [t + t1]
    FF      -> error "(bug) FF in NormPred"

normal :: NormProp -> Term -> Prop
normal prop t = case prop of
  Ind p -> p
  L ps@(Pred (Divs {}) _) t1  -> ps :> [t + t1]
  L ps t1                     -> ps :> [t,t1]


data Ex = Ex [(Name,Integer)]
             [(Integer,Term)]
             [Prop]
             ([Prop] -> Form)

instance PP Ex where
  pp (Ex xs ps ss _) = hang (text "OR" <+> hsep (map quant xs)) 2
             ( text "!" <+> hsep (map (parens . divs) ps)
            $$ vcat (map pp ss)
             )
    where quant (x,n) = parens $ text (var_name x) <> colon <> text (show n)
          divs (x,t)  = text (show x) <+> text "|" <+> pp t




ex_base :: Form -> Ex
ex_base f = Ex [] [] ps skel
  where (ps,skel) = abs_form f

ex_step :: Name -> Ex -> [Ex]
ex_step x (Ex xs ds ps skel) = if longer_or_equal as bs then ver_b else ver_a
  where (ps1,k,d,as,bs) = analyze_props x ps
        ver_a = ( let arg = negate (var x)
                  in Ex ((x,d)   : xs)
                        ((k,arg) : ds)
                        (map (`pos_inf` arg) ps1)
                        skel
                ) : [ let arg = a - var x
                      in Ex ((x,d) : xs)
                            ((k,arg) : ds)
                            (map (`normal` arg) ps1)
                            skel 
                       | a <- as ]
        ver_b = ( let arg = var x
                  in Ex ((x,d)   : xs)
                        ((k,arg) : ds)
                        (map (`neg_inf` arg) ps1)
                        skel
                ) : [ let arg = b + var x
                      in Ex ((x,d) : xs)
                            ((k,arg) : ds)
                            (map (`normal` arg) ps1)
                            skel 
                       | b <- bs ]



expand :: Ex -> Form
expand e | trace (show (pp e)) False = undefined
expand (Ex xs ds ps skel) = ors'
                       $ [ foldl and' f1 qs
                            | env <- mk xs
                            , let qs = map (divs env) ds
                            , let f1 = skel (map (subst_prop env) ps)
                         ]
  where divs env (x,a)  = Prop $ Pred (Divs x) True :> [ subst_term env a ]
        mk ((x,d):qs)   = [ Map.insert x n m | m <- mk qs, n <- [ 1 .. d ] ]
        mk []           = [ Map.empty ]

type Env = Map.IntMap Integer

subst_prop :: Env -> Prop -> Prop
subst_prop env (p :> ts) = p :> map (subst_term env) ts

subst_term :: Env -> Term -> Term
subst_term env (Term m n) =
  let (xs,vs) = unzip $ Map.toList $ Map.intersectionWith (*) env m
  in Term (foldl' (flip Map.delete) m xs) (foldl' (+) n vs)

exists_many :: [Name] -> Form -> Form
exists_many xs f  = ors'
                  $ map expand 
                  $ foldr (concatMap . ex_step) [ex_base f] xs



-- Evaluation ------------------------------------------------------------------

eval_form :: Form -> Bool
eval_form (Conn c p q) = eval_conn c (eval_form p) (eval_form q)
eval_form (Prop p)     = eval_prop p

eval_conn :: Conn -> Bool -> Bool -> Bool
eval_conn And = (&&)
eval_conn Or  = (||)

eval_prop :: Prop -> Bool
eval_prop (Pred p pos :> ts) = if pos then res else not res
  where res = eval_pred p (map eval_term ts)

eval_pred :: PredSym -> [Integer] -> Bool
eval_pred FF []         = False
eval_pred (Divs d) [k]  = mod k d == 0
eval_pred LT [x,y]      = x < y
eval_pred LEQ [x,y]     = x <= y
eval_pred EQ [x,y]      = x == y
eval_pred _ _           = error "Type error"

-- There should be no free variables.
eval_term :: Term -> Integer
eval_term (Term _ k) = k


--------------------------------------------------------------------------------

-- Misc -----------------------------------------------------------------------

longer_or_equal :: [a] -> [a] -> Bool
longer_or_equal (_:xs) (_:ys) = longer_or_equal xs ys
longer_or_equal [] (_:_)      = False
longer_or_equal _ _           = True

lcms :: Integral a => [a] -> a
lcms xs = foldr lcm 1 xs
