module Syntax where

data Formula p  = FF
                | TT
                | And (Formula p) (Formula p)
                | Or  (Formula p) (Formula p)
                | Prop p
                  deriving Show

conj           :: Formula p -> Formula p -> Formula p
conj FF _       = FF
conj TT x       = x
conj _ FF       = FF
conj x TT       = x
conj x y        = And x y

disj           :: Formula p -> Formula p -> Formula p
disj FF x       = x
disj TT _       = TT
disj x FF       = x
disj _ TT       = TT
disj x y        = Or x y

neg            :: (p -> p) -> Formula p -> Formula p
neg p f = case f of
  FF          -> TT
  TT          -> FF
  And x y     -> Or  (neg p x) (neg p y)
  Or x y      -> And (neg p x) (neg p y)
  Prop x      -> Prop (p x)

abs_prop      :: Formula p -> ([p], [Formula q] -> Formula q)
abs_prop a      = let (ps,f) = loop [] a
                  in (reverse ps, fst . f)

  where
  loop ps f = case f of
                FF          -> (ps, \fs -> (FF,fs))
                TT          -> (ps, \fs -> (TT,fs))
                Prop p      -> (p:ps, \(q:qs) -> (q,qs))
                And x y     -> bin conj ps x y
                Or  x y     -> bin disj ps x y

  bin f ps x y = let (px,fx) = loop ps x
                     (py,fy) = loop px y
                 in (py, \qs -> let (x1,qs1) = fx qs
                                    (y1,qs2) = fy qs1
                                in (f x1 y1,qs2))






