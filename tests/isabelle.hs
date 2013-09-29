{- The first examples are Translated from:
HOL/ex/PresburgerEx.thy by Amine Chaieb, TU Muenchen

We added more as needed.
-}

import Data.Integer.Presburger


main = print $ isTrue ex21

allOk = all isTrue [ ex1, ex2, ex3, ex4, ex5
                   , ex6, ex7, ex8, ex9, ex10
                   ,      ex12, ex13, ex14, ex15
                   , ex16, ex17, ex18, ex19, ex20

                   , ex30, ex31, ex32, ex33, ex34
                   , ex35, ex36, ex37
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


ex30 = bForAll nat $ \emBits ->
       letDivMod emBits 8 $ \q r ->
       0 |<| r ==> 8 + q * 8 - emBits |==| 8 - r

--hm?
ex31 = bForAll nat $ \x ->
       bExists nat $ \y ->
       y |==| 5 + x \/
       letDivMod x 6 (\q _ -> q + 1 |==| 2)

ex32 = bForAll nat $ \x ->
       bExists nat $ \y ->
       letDivMod x 6 (\q _ ->
       y |==| 5 + x \/  q + 1 |==| 2)

ex33 = bForAll nat $ \n -> (bExists nat $ \m -> n |==| 2 * m) ==>
                           (letDivMod (n + 1) 2 $ \q1 _ ->
                            letDivMod n       2 $ \q2 _ ->
                            q1 |==| q2)

ex34 = neg $ forAll $ \x ->
  (divides 2 x <==> (forAll $ \y -> x |/=| 2 * y + 1)) \/
  (exists $ \q u i -> 3 * i + 2 * q - u |<| 17)
  ==> 0 |<| x \/ (neg (divides 3 x) /\ (x + 8 |==| 0))


ex35 = bForAll nat $ \m n i j ja e ->
  neg (m |<=| j) /\
  neg (n |<=| i) /\
  e |/=| 0 /\
  1 + j |<=| ja
  ==>
  (bExists nat $ \m ->
  bForAll nat $ \ja ia ->
    m |<=| ja ==> tITE (j |==| ja /\ i |==| ia) e 0 |==| 0)

ex36 = letDivMod 5 2 $ \q r -> q |==| 2 /\ r |==| 1
ex37 = forAll $ \x -> neg $ letDivMod x 0 $ \_ _ -> true






