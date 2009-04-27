import Data.Integer.Presburger
import Debug.Trace


l = 16 * 8 * 8

given :: Formula
given = forall $ \a b -> l .* b - 8 .* a :>=: 65

divided :: Term -> Integer -> (Term -> Term -> Formula) -> Formula
divided t k body = exists $ \q r ->
        0 :<=: r
   :/\: r :<: fromInteger k
   :/\: k .* q + r :=: t
   :/\: body q r


inferred = forall $ \a b ->
           divided (8 .* a + 64) l $ \q r ->
              l .* q - 8 .* a + fromInteger l - 65 :>=: 0  :/\:
              b :=: 1 + q


main = print $ check (inferred :<=>: given)




