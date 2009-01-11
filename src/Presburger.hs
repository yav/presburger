{-# LANGUAGE FlexibleInstances #-}

{-| This module implements Cooper's algorithm for deciding
    first order formulas over integers with addition.

Based on the paper:
 * author: D.C.Cooper
 * title:  "Theorem Proving in Arithmetic without Multiplication"
 * year:   1972
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

{-
class Quantified a where
  exists' :: Int -> a -> Form
  forall' :: Int -> a -> Form


instance Quantified Form where
  exists' n f = exists_many [1 .. n] f
  forall' n f = not' $ exists_many [1 .. n] $ not' f

instance Quantified t => Quantified (Term -> t) where
  exists' n f = exists' (n+1) (f (var n))
  forall' 
    

instance Quantified t => Quantified (Term -> t) where
  exists' xs f = F $ \x -> let F g = exists' (x:xs) (f (var x)) in g (x+1)

-- | Check for the existance of an integer that satisfies the formula.
exists             :: Quantified t => t -> Form
exists f            = exists' 0 f

-- | Check if all integers satisfy the formula.
forall             :: Quantified t => t -> Form
forall t            = not' $ exists $ \x -> not' (t x)

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

-- | @split_term x (n * x + t1) = (n,t1)
-- @x@ does not occur in @t1@
split_term         :: Name -> Term -> (Integer,Term)
split_term x (Term m n) = (fromMaybe 0 c, Term m1 n)
  where (c,m1) = Map.updateLookupWithKey (\_ _ -> Nothing) x m

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

-- Eliminating existential quantifiers -----------------------------------------


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

  where (k1,t1') = split_term x t1
        (k2,t2') = split_term x t2

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

  where (k,t')  = split_term x t
        l       = final_k `div` k
        ps      = Pred (Divs (d * abs l)) b

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

-- | The integer is "length as - length bs"
a_b_sets :: (Integer,[Term],[Term]) -> NormProp -> (Integer,[Term],[Term])
a_b_sets (o,as,bs) p = case p of
  Ind _ -> (o,as,bs)

  L (Pred op True) t ->
    case op of
      LT  -> (1 + o , t     : as,         bs)
      LEQ -> (1 + o , (t+1) : as,         bs)
      EQ  -> (o     , (t+1) : as, (t-1) : bs)
      _   -> (o     ,         as,         bs)

  L (Pred op False) t ->
    case op of
      LT  -> (o - 1 ,         as, (t-1) : bs)
      LEQ -> (o - 1 ,         as, t     : bs)
      EQ  -> (o     , t     : as, t     : bs)
      _   -> (o     ,         as,         bs)


analyze_props :: Name -> [Prop] -> ( [NormProp]
                                   , Integer    -- scale
                                   , Integer    -- bound
                                   , Either [Term] [Term]  -- A set or B set
                                   )
analyze_props x ps = (ps1, final_k, bnd, if o < 0 then Left as else Right bs)
  where (ks,ps1)  = unzip $ map (norm_prop x final_k) ps
        final_k   = lcms ks
        (o,as,bs) = foldl' a_b_sets (0,[],[]) ps1
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
             [Constraint]
             [Prop]

instance PP Ex where
  pp (Ex xs ps ss) = hang (text "OR" <+> hsep (map quant xs)) 2
             ( text "!" <+> hsep (map (parens . divs) ps)
            $$ vcat (map pp ss)
             )
    where quant (x,n) = parens $ text (var_name x) <> colon <> text (show n)
          divs (x,t)  = text (show x) <+> text "|" <+> pp t

exists_many :: [Name] -> Form -> Form
exists_many xs f  = ors'
                  $ map (expand skel)
                  $ foldr (concatMap . ex_step) [Ex [] [] ps] xs
  where (ps,skel) = abs_form f


ex_step :: Name -> Ex -> [Ex]
ex_step x (Ex xs ds ps) = case as_or_bs of
  Left as -> 
    ( let arg = negate (var x)
      in Ex ((x,d) : xs) ((k,arg) : ds) (map (`pos_inf` arg) ps1)
    ) : [ let arg = a - var x
          in Ex ((x,d) : xs) ((k,arg) : ds) (map (`normal` arg) ps1) | a <- as ]

  Right bs ->
    ( let arg = var x
      in Ex ((x,d) : xs) ((k,arg) : ds) (map (`neg_inf` arg) ps1)
    ) : [ let arg = b + var x
          in Ex ((x,d) : xs) ((k,arg) : ds) (map (`normal` arg) ps1) | b <- bs ]

  where (ps1,k,d,as_or_bs) = analyze_props x ps


expand :: ([Prop] -> Form) -> Ex -> Form
expand _ e | trace (show (pp e)) False = undefined
expand skel (Ex xs ds ps) =
  ors' [ skel (map (subst_prop env) ps) | env <- elim xs ds ]



type Env = Map.IntMap Integer

subst_prop :: Env -> Prop -> Prop
subst_prop env (p :> ts) = p :> map (subst_term env) ts

subst_term :: Env -> Term -> Term
subst_term env (Term m n) =
  let (xs,vs) = unzip $ Map.toList $ Map.intersectionWith (*) env m
  in Term (foldl' (flip Map.delete) m xs) (foldl' (+) n vs)




-- Evaluation ------------------------------------------------------------------

-- The meanings of formulas.
eval_form :: Form -> Bool
eval_form (Conn c p q) = eval_conn c (eval_form p) (eval_form q)
eval_form (Prop p)     = eval_prop p

-- The meanings of connectives.
eval_conn :: Conn -> Bool -> Bool -> Bool
eval_conn And = (&&)
eval_conn Or  = (||)

-- The meanings of atomic propositions.
eval_prop :: Prop -> Bool
eval_prop (Pred p pos :> ts) = if pos then res else not res
  where res = eval_pred p (map eval_term ts)

-- The meanings of predicate symbols.
eval_pred :: PredSym -> [Integer] -> Bool
eval_pred p ts = case (p,ts) of
  (FF,     [])    -> False
  (Divs d, [k])   -> divides d k
  (LT,     [x,y]) -> x < y
  (LEQ,    [x,y]) -> x <= y
  (EQ,     [x,y]) -> x == y
  _               -> error "Type error"

-- We define: "d | a" as "exists y. d * y = a"
divides :: Integral a => a -> a -> Bool
0 `divides` 0 = True
0 `divides` _ = False
x `divides` y = mod y x == 0

-- The meaning of a term with no free variables.
-- NOTE: We do not check that there are no free variables.
eval_term :: Term -> Integer
eval_term (Term _ k) = k

-- The meaning of a term with free variables
eval_term_env :: Term -> Env -> Integer
eval_term_env (Term m k) env = sum (k : map eval_var (Map.toList m))
  where eval_var (x,c) = case Map.lookup x env of
                           Nothing -> 0
                           Just v  -> c * v
--------------------------------------------------------------------------------


-- Solving divides constraints -------------------------------------------------
-- See the paper's appendix.


-- | let (p,q,r) = extended_gcd x y
--   in (x * p + y * q = r)  &&  (gcd x y = r)
extended_gcd :: Integral a => a -> a -> (a,a,a)
extended_gcd arg1 arg2 = loop arg1 arg2 0 1 1 0
  where loop a b x lastx y lasty
          | b /= 0    = let (q,b') = divMod a b
                            x'     = lastx - q * x
                            y'     = lasty - q * y
                        in x' `seq` y' `seq` loop b b' x' x y' y
          | otherwise = (lastx,lasty,a)


type Constraint     = (Integer,Term)
type VarConstraint  = (Integer,Integer,Term)

-- m | (x * a1 + b1) /\ (n | x * a2 + b2)
theorem1 :: VarConstraint -> VarConstraint -> (VarConstraint, Constraint)
theorem1 (m,a1,b1) (n,a2,b2) = (new_x, new_other)
  where new_x     = (m * n, d, (p*n) .* b1 + (q * m) .* b2)
        new_other = (d, a2 .* b1 - a1 .* b2)

        (p,q,d)   = extended_gcd (a1 * n) (a2 * m)

-- solutions for x in [1 .. bnd] of: m | x * a + b
theorem2 :: Integer -> (Integer,Integer,Integer) -> [Integer]
theorem2 bnd (m,a,b)
  | r == 0      = [ t * k - c | t <- [ lower .. upper ] ]
  | otherwise   = []
  where k           = div m d
        c           = p * qu
        (p,_,d)     = extended_gcd a m
        (qu,r)      = divMod b d

        (lower',r1) = divMod (1 + c) k
        lower       = if r1 == 0 then lower' else lower' + 1  -- hmm
        upper       = div (bnd + c) k

  -- lower and upper:
  -- t * k - c = 1   --> t = (1 + c) / k
  -- t * k - c = bnd --> t = (bnd + c) / k

elim :: [(Name,Integer)] -> [Constraint] -> [ Env ]
elim [] ts = if all chk ts then [ Map.empty ] else []
  where chk (x,t) = divides x (eval_term t)
elim ((x,bnd):xs) cs = do env <- elim xs cs1
                          v <- case mb of
                                 Nothing      -> [ 1 .. bnd ]
                                 Just (a,b,t) ->
                                   theorem2 bnd (a,b,eval_term_env t env)
                          return (Map.insert x v env)
                                               
  where (mb,cs1) = elim_var x cs
          



elim_var :: Name -> [Constraint] -> (Maybe VarConstraint, [Constraint])
elim_var x cs = case foldl' part ([],[]) cs of
                  ([], have_not)     -> (Nothing, have_not)
                  (h : hs, have_not) -> let (c,hn) = step h hs have_not
                                        in (Just c,hn)
  where part s@(have,have_not) c@(m,t) 
          | m == 1      = s
          | a == 0      = (have        , c:have_not)
          | otherwise   = ((m,a,b):have,   have_not)
            where (a,b) = split_term x t

        step :: VarConstraint -> [VarConstraint] -> [Constraint]
             -> (VarConstraint,[Constraint])
        step h [] ns      = (h,ns)
        step h (h1:hs) ns = step h2 hs (n : ns)
          where (h2,n) = theorem1 h h1

-- Misc -----------------------------------------------------------------------

lcms :: Integral a => [a] -> a
lcms xs = foldr lcm 1 xs
