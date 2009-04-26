import Data.Integer.Presburger
import Debug.Trace


l = 16 * 8 * 8

given :: Formula
given = Forall $ \a ->
        Forall $ \b ->
            l .* b - 8 .* a :>=: 65

divided :: Term -> Integer -> (Term -> Term -> Formula) -> Formula
divided t k body =
  Exists $ \q ->
  Exists $ \r ->
        0 :<=: r
   :/\: r :<: fromInteger k
   :/\: k .* q + r :=: t
   :/\: body q r


inferred = Forall $ \a ->
           Forall $ \b ->
           divided (8 .* a + 64) l $ \q r ->
              l .* q - 8 .* a + fromInteger l - 65 :>=: 0  :/\:
              b :=: 1 + q


test1 = inferred :<=>: given




