{-| This module implements Cooper's algorithm for deciding
    first order formulas over integers with addition.

Based on the paper:
  author: D.C.Cooper
  title:  "Theorem Proving in Arithmetic without Multiplication"
  year:   1972
-}
module Presburger
  ( check, check_val

  , Term
  , num
  , (.+.), (.+), (+.)
  , (.-.), (.-), (-.)
  , (.*), (*.)
  , neg

  , Formula
  , false, (\/)
  , true, (/\)
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
import Debug.Trace


-- | Decide the validity of a formula.
check              :: Formula -> Bool
check (F f)         = eval_form Map.empty (f 0)

check_val          :: Formula -> [Env]
check_val (F f)     = eval_top Map.empty (f 0)


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
m .-. n             = m .+. neg n

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
false               = lift FF

-- | True formula.
true               :: Formula
true                = lift TT

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
t1 .<. t2           = lift $ Pred (Op2 LessThen t1 t2)

infix 4 .<=.
-- | Check if one term is smaller then, or equal to another.
(.<=.)             :: Term -> Term -> Formula
t1 .<=. t2          = lift $ Pred (Op2 LessThenEqual t1 t2)

infix 4 .>.
-- | Check if one term is strictly greater then another.
(.>.)              :: Term -> Term -> Formula
t1 .>. t2           = t2 .<. t1

infix 4 .>=.
-- | Check if one term is greater-then, or equal to another.
(.>=.)             :: Term -> Term -> Formula
t1 .>=. t2          = t2 .<=. t1

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

data QInfo      = QInfo { qName   :: Name
                        , qBound  :: Integer
                        }

data Ev         = Ev { qVal   :: Term
                     , qScale :: Integer
                     }

data Form p     = And (Form p) (Form p)
                | Or  (Form p) (Form p)
                | TT
                | FF
                | Exists QInfo [(Ev,Form p)]   -- expands to OR, body OR
                | All    QInfo [(Ev,Form p)]   -- expands to AND, body AND
                | Pred p

and' :: Form p -> Form p -> Form p
and' FF _ = FF
and' TT x = x
and' (And x y) z = and' x (and' y z)
and' _ FF = FF
and' x TT = x
and' x y  = And x y

or' :: Form p -> Form p -> Form p
or' TT _ = TT
or' FF x = x
or' (Or x y) z = or' x (or' y z)
or' _ TT = TT
or' x FF = x
or' x y  = Or x y


instance PP Pred where
  pp (Op2 op t1 t2) = pp t1 <+> pp op <+> pp t2
  pp (Op1 op t1)    = pp op <+> pp t1

instance PP VarPred where
  pp (VOp2 op t1) = text "_" <+> pp op <+> pp t1
  pp (VOp1 op t1) = pp op <+> text "_ +" <+> pp t1
  pp (GreaterThen t)  = text "_ >" <+> pp t
  pp (GreaterThenEqual t)  = text "_ >=" <+> pp t
  pp (Independent p)  = pp p

instance PP Op1 where
  pp (Divides x)    = text (show x) <+> char '|'
  pp (NotDivides x) = text (show x) <+> text "/|"

instance PP Op2 where
  pp LessThen       = text "<"
  pp LessThenEqual  = text "<="
  pp Equal          = text "="
  pp NotEqual       = text "/="

instance PP Ev where
  pp (Ev t 1)       = pp t
  pp (Ev t n)       = pp t <+> text "/" <+> text (show n)

instance PP p => PP (Form p) where
  pp fo = case fo of
    TT      -> text "True"
    FF      -> text "False"
    And x y -> hang (text "AND") 2 (vcat [ pp x, pp y ])
    Or  x y -> hang (text "OR")  2 (vcat [ pp x, pp y ])
    Exists x fs -> hang (text "OR" <+> text (var_name (qName x))
                        <+> text "= 1 .." <+> text (show (qBound x))) 2
                              (vcat [ pp ev <> colon <+> pp f | (ev,f) <- fs ])

    All x fs    -> hang (text "AND" <+> text (var_name (qName x))
                        <+> text "= 1 .." <+> text (show (qBound x))) 2
                              (vcat [ pp ev <> colon <+> pp f | (ev,f) <- fs ])
    Pred p  -> pp p

instance PP Formula where
  pp (F f)  = pp (f 0)


not' :: Form Pred -> Form Pred
not' t = case t of
  TT      -> FF
  FF      -> TT
  And p q -> Or (not' p) (not' q)
  Or  p q -> And (not' p) (not' q)
  Exists x fs -> All x    [ (ev, not' f) | (ev, f) <- fs ]
  All x    fs -> Exists x [ (ev, not' f) | (ev, f) <- fs ]
  Pred p -> Pred $ case p of
    Op2 op t1 t2 -> case op of
      LessThen      -> Op2 LessThenEqual t2 t1
      LessThenEqual -> Op2 LessThen t2 t1
      Equal         -> Op2 NotEqual t1 t2
      NotEqual      -> Op2 Equal t1 t2
    Op1 op t1 -> case op of
      Divides k     -> Op1 (NotDivides k) t1
      NotDivides k  -> Op1 (Divides k) t1


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

occurs _ TT             = False
occurs _ FF             = False
occurs x (And p q)      = occurs x p || occurs x q
occurs x (Or p q)       = occurs x p || occurs x q
occurs x (Exists _ fs)  = any (occurs x . snd) fs
occurs x (All _ fs)     = any (occurs x . snd) fs
occurs x (Pred p)       = occurs_pred x p

occurs_pred x (Op2 _ t1 t2) = occurs_term x t1 || occurs_term x t2
occurs_pred x (Op1 _ t1)    = occurs_term x t1

occurs_term x t             = coeff x t /= 0

-- NOTE: When equal use one with fewer variables?
exists' :: Name -> Form Pred -> Form Pred
exists' _ TT            = TT
exists' _ FF            = FF
exists' x (Or p q)      = Or (exists' x p) (exists' x q)
exists' x (Exists y fs) = Exists y [ (ev, exists' x f) | (ev,f) <- fs ]
exists' x (And p q)
  | not (occurs x p)    = And p (exists' x q)
  | not (occurs x q)    = and' (exists' x p) q

exists' x t = let (t1,d,k,as,bs) = analyze x t
              in if longer_or_equal as bs
                    then ver_b d k t1 bs
                    else ver_a d k t1 as

  where
  ver_a d k f as = -- trace ("USING A: " ++ unwords (map (show.pp) as)) $
    Or ( let ev = neg (var x)
         in Exists (QInfo x d) [ (Ev ev k, body pos_inf x ev f) ]
       )
       ( Exists (QInfo x d) $
           [ (Ev ev k, body normal x ev f) | a <- as, let ev = a .-. var x ]
       )

  ver_b d k f bs = -- trace ("USING B: " ++ unwords (map (show.pp) bs)) $
    Or ( let ev = var x
         in Exists (QInfo x d) [ (Ev ev k, body neg_inf x ev f) ]
       )
       ( Exists (QInfo x d)
          [ (Ev ev k, body normal x ev f) | b <- bs, let ev = b .+. var x ]
       )


var :: Name -> Term
var x = Term (Map.singleton x 1) 0


expand_q :: ([Form p] -> Form p)
         -> (Name -> Integer -> p -> p)
         -> QInfo -> [(Ev,Form p)] -> Form p
expand_q mk su x fs = mk [ subst su (qName x) n f | n <- [ 1 .. qBound x ],
                                                    (_,f) <- fs
                         ]

subst :: (Name -> Integer -> p -> p)
      -> Name -> Integer -> Form p -> Form p
subst su x n fo = case fo of
  TT          -> TT
  FF          -> FF
  And p q     -> And (subst su x n p) (subst su x n q)
  Or  p q     -> Or  (subst su x n p) (subst su x n q)
  Exists q fs -> Exists q [ (subst_ev x n ev, subst su x n f) | (ev,f) <- fs ]
  All    q fs -> All q    [ (subst_ev x n ev, subst su x n f) | (ev,f) <- fs ]
  Pred p      -> Pred (su x n p)

subst_pred :: Name -> Integer -> Pred -> Pred
subst_pred x n p = case p of
  Op2 op t1 t2 -> Op2 op (subst_term x n t1) (subst_term x n t2)
  Op1 op t1    -> Op1 op (subst_term x n t1)

subst_ev :: Name -> Integer -> Ev -> Ev
subst_ev x n ev = ev { qVal = subst_term x n (qVal ev) }

subst_ev' :: Name -> Term -> Ev -> Ev
subst_ev' x n ev = ev { qVal = subst_term' x n (qVal ev) }

subst_term :: Name -> Integer -> Term -> Term
subst_term x n (Term m k) =
 case Map.updateLookupWithKey (\_ _ -> Nothing) x m of
   (mbv,m1) -> Term m1 (maybe k (\v -> n * v + k) mbv)

subst_term' :: Name -> Term -> Term -> Term
subst_term' x n t = coeff x t *. n .+. rm_var x t



analyze :: Name -> Form Pred
        -> ( Form VarPred     -- Normalized formula
           , Integer          -- delta
           , Integer          -- scale
           , [Term]           -- A set
           , [Term]           -- B set
           )


analyze x term = ( And t1 (Pred $ VOp1 (Divides final_k) (num 0))
                 , d1, final_k, as1, bs1)

  where (t1, final_k, d1, as1, bs1) = loop term

        loop f = trace ("LOOP: " ++ var_name x ++ "\n " ++ show (pp f)) $ case f of
          TT -> (TT, 1, 1, [], [])
          FF -> (FF, 1, 1, [], [])

          And p q -> let (f1,k1,d1,as1,bs1) = loop p
                         (f2,k2,d2,as2,bs2) = loop q
                     in (And f1 f2, lcm k1 k2, lcm d1 d2
                        , as1 ++ as2, bs1 ++ bs2
                        )

          Or p q  -> let (f1,k1,d1,as1,bs1) = loop p
                         (f2,k2,d2,as2,bs2) = loop q
                     in (Or f1 f2, lcm k1 k2, lcm d1 d2
                        , as1 ++ as2, bs1 ++ bs2
                        )

           --- XXX
          Exists q a -> loop (expand_q (foldr or' FF) subst_pred q a)
          --- All q a    -> loop (expand_q (foldr and' TT) subst_pred q a)

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

-- Assumes no shadowing of quantifiers
body :: (VarPred -> Term -> Form Pred) -> Name -> Term -> Form VarPred
      -> Form Pred
body how x t fo = case fo of
  TT         -> TT
  FF         -> FF
  Pred p     -> how p t
  And f1 f2  -> and' (body how x t f1) (body how x t f2)
  Or  f1 f2  -> or'  (body how x t f1) (body how x t f2)
  Exists y fs ->
    Exists y [ (subst_ev' x t ev, body how x t f) | (ev,f) <- fs ]
  All y fs ->
    All y    [ (subst_ev' x t ev, body how x t f) | (ev,f) <- fs ]

normal :: VarPred -> Term -> Form Pred
normal p t = case p of
  VOp2 op t1          -> Pred $ Op2 op t t1
  GreaterThen t1      -> Pred $ Op2 LessThen t1 t
  GreaterThenEqual t1 -> Pred $ Op2 LessThenEqual t1 t
  VOp1 (Divides 1) _     -> TT
  VOp1 (NotDivides 1) _  -> FF
  VOp1 op t1          -> Pred $ Op1 op (t .+. t1)
  Independent p1      -> Pred p1

neg_inf :: VarPred -> Term -> Form Pred
neg_inf p t = case p of
  VOp2 op _           -> case op of
    LessThen          -> TT
    LessThenEqual     -> TT
    Equal             -> FF
    NotEqual          -> TT
  GreaterThen {}      -> FF
  GreaterThenEqual {} -> FF
  VOp1 (Divides 1) _  -> TT
  VOp1 (NotDivides 1) _ -> FF
  VOp1 op t1          -> Pred (Op1 op (t .+. t1)) -- depends on var.
  Independent p1      -> Pred p1

pos_inf :: VarPred -> Term -> Form Pred
pos_inf p t = case p of
  VOp2 op _           -> case op of
    LessThen          -> FF
    LessThenEqual     -> FF
    Equal             -> FF
    NotEqual          -> TT
  GreaterThen {}      -> TT
  GreaterThenEqual {} -> TT
  VOp1 (Divides 1) _  -> TT
  VOp1 (NotDivides 1) _ -> FF
  VOp1 op t1          -> Pred (Op1 op (t .+. t1)) -- depends on var.
  Independent p1      -> Pred p1



-- Evaluation ------------------------------------------------------------------

type Env = Map.IntMap Integer

extend :: Name -> Integer -> Env -> Env
extend x y = Map.insert x y


eval_top :: Env -> Form Pred -> [Env]
eval_top env TT         = [ env ]
eval_top _ FF           = []
eval_top env (Or p q)   = eval_top env p ++ eval_top env q
eval_top env (And p q)  = [ Map.union a1 a2 | a1 <- eval_top env p
                                            , a2 <- eval_top env q ]

eval_top env (Exists x fs) =
  [ ans | n      <- [ 1 .. qBound x ],
          (ev,f) <- fs,
          ans    <- eval_top (extend (qName x) n env) f
  ]
eval_top env (All x fs) = map Map.unions $ sequence
  [ ans | n      <- [ 1 .. qBound x ],
          (ev,f) <- fs,
          let ans = eval_top (extend (qName x) n env) f
  ]

eval_top env (Pred p)
  | eval_pred env p = [ env ]
  | otherwise       = []    -- report counter example

eval_form :: Env -> Form Pred -> Bool
eval_form env fo = case fo of
  TT            -> True
  FF            -> False
  And p q       -> eval_form env p && eval_form env q
  Or  p q       -> eval_form env p || eval_form env q
  Exists q fs   -> or [ eval_form (extend (qName q) n env) f
                                            | (_,f) <- fs,
                                              n <- [ 1 .. qBound q ] ]
  All q fs      -> and [ eval_form (extend (qName q) n env) f
                                            | (_,f) <- fs,
                                              n <- [ 1 .. qBound q ] ]
  Pred p        -> eval_pred env p

eval_pred :: Env -> Pred -> Bool
eval_pred env p = case p of
  Op2 op t1 t2  -> eval_op2 op (eval_term env t1) (eval_term env t2)
  Op1 op t1     -> eval_op1 op (eval_term env t1)

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

eval_term :: Env -> Term -> Integer
eval_term env (Term m k) = sum (k : map evvar (Map.toList m))
  where evvar (x,n) = n * Map.findWithDefault 0 x env


--------------------------------------------------------------------------------



-- Misc -----------------------------------------------------------------------

longer_or_equal :: [a] -> [a] -> Bool
longer_or_equal (_:xs) (_:ys) = longer_or_equal xs ys
longer_or_equal [] (_:_)      = False
longer_or_equal _ _           = True



