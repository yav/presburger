


{- Translated from:
Title:      HOL/ex/PresburgerEx.thy
Author:     Amine Chaieb, TU Muenchen
-}

import Data.Integer.Presburger


main = print $ isTrue ex21

allOk = all isTrue [ ex1, ex2, ex3, ex4, ex5
                   , ex6, ex7, ex8, ex9, ex10
                   ,      ex12, ex13, ex14, ex15
                   , ex16, ex17, ex18, ex19, ex20
                   ]


ex1 = exists $ \x -> 0 |<| x

ex2 = forAll $ \a b ->
        (forAll $ \y -> divides 3 y) ==> forAll (\x -> b |<| x ==> a |<| x)

ex3 = forAll $ \y z ->
      divides 3 z ==>
      divides 2 y ==>
      exists (\x -> 2 * x |==| y) /\
      exists (\k -> 3 * k |==| z)

ex4 = forAll $ \y z n ->
      (1 + n |<| 6) ==>
      (divides 3 z) ==>
      (divides 2 y) ==>
      (exists $ \x -> 2 * x |==| y) /\
      (exists $ \k -> 3 * k |==| z)

ex5 = bForAll nat $ \x ->
      bExists nat $ \y -> 0 |<=| 5 ==> y |==| 5 + x

ex6 = forAll $ \x y -> x |<| y ==> 2 * x + 1 |<| 2 * y

ex7 = exists $ \x y -> 0 |<| x /\ 0 |<=| 0 /\ 3 * x - 5 * y |==| 1

ex8 = forAll $ \x y -> 2 * x + 1 |/=| 2 * y

ex9 = neg $ exists $ \x y -> 4 * x + (-6) * y |==| 1

ex10 = neg $ forAll $ \a b x -> b |<| x ==> a |<=| x

ex12 = neg $ exists $ \x -> false

ex13 = neg $ forAll $ \x a b -> a |<| 3 * x ==> b |<| 3 * x

ex14 = forAll $ \x -> divides 2 x ==> exists (\y -> x |==| 2 * y)

ex15 = forAll $ \x -> divides 2 x <==> exists (\y -> x |==| 2 * y)

ex16 = forAll $ \x -> divides 2 x <==> forAll (\y -> x |/=| 2 * y + 1)

ex17 = neg $ forAll $ \i -> 4 |<=| i ==>
       (exists $ \x y -> 0 |<=| x /\ 0 |<=| y /\ 3 * x + 5 * y |==| i)

ex18 = forAll $ \i -> 8 |<=| i ==>
       (exists $ \x y -> 0 |<=| x /\ 0 |<=| y /\ 3 * x + 5 * y |==| i)

ex19 = exists $ \j -> forAll $ \i -> j |<=| i ==>
       (exists $ \x y -> 0 |<=| x /\ 0 |<=| y /\ 3 * x + 5 * y |==| i)

ex20 = neg $ forAll $ \j i -> j |<=| i ==>
       (exists $ \x y -> 0 |<=| x /\ 0 |<=| y /\ 3 * x + 5 * y |==| i)


-- HARD!
ex21 = forAll $ \x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ->
        x3  |==| abs x2  - x1 /\
        x4  |==| abs x3  - x2 /\
        x5  |==| abs x4  - x3 /\
        x6  |==| abs x5  - x4 /\
        x7  |==| abs x6  - x5 /\
        x8  |==| abs x7  - x6 /\
        x9  |==| abs x8  - x7 /\
        x10 |==| abs x9  - x8 /\
        x11 |==| abs x10 - x9 ==>
        x1 |==| x10 /\ x2 |==| x11



{-
lemma "\<And>m n ja ia. [| ~ m <=  j;
                                 ~ (n::nat) <=  i;
                                 (e::nat) /= 0;
                                 Suc j <=  ja|] 
    ==>  exists m. forall ja ia. m <=  ja -->  (if j = ja && i = ia then e else 0) = 0" by presburger


lemma "(0::nat) < emBits mod 8 ==>  8 + emBits div 8 * 8 - emBits = 8 - emBits mod 8" 
by presburger

lemma "(0::nat) < emBits mod 8 ==>  8 + emBits div 8 * 8 - emBits = 8 - emBits mod 8" 
by presburger
-}

{-



text{*Slow: about 7 seconds on a 1.6GHz machine.*}
theorem "forall (x::nat). exists (y::nat). y = 5 + x | x div 6 + 1= 2"
  by presburger


theorem "~ (forall (x::int). 
            ((2 dvd x) = (forall (y::int). x /= 2*y+1) | 
             (exists (q::int) (u::int) i. 3*i + 2*q - u < 17)
             --> 0 < x | ((~ 3 dvd x) &(x + 8 = 0))))"
  by presburger
 
text{*Slow: about 5 seconds on a 1.6GHz machine.*}
theorem "(exists m::nat. n = 2 * m) --> (n + 1) div 2 = n div 2"
  by presburger

text{* This following theorem proves that all solutions to the
recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
period 9.  The example was brought to our attention by John
Harrison. It does does not require Presburger arithmetic but merely
quantifier-free linear arithmetic and holds for the rationals as well.

Warning: it takes (in 2006) over 4.2 minutes! *}

lemma "[|  x3 = abs x2 - x1; x4 = abs x3 - x2; x5 = abs x4 - x3;
         x6 = abs x5 - x4; x7 = abs x6 - x5; x8 = abs x7 - x6;
         x9 = abs x8 - x7; x10 = abs x9 - x8; x11 = abs x10 - x9 |] 
 ==>  x1 = x10 & x2 = (x11::int)"
by arith
-}
