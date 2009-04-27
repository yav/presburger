import Data.Integer.Presburger.ModArith
import Data.Integer.Presburger

main = print $ check $ forall $ \x y z1 z2 ->
          (add_mod d x y z1 :/\: add_mod d x y z2) :=>: z1 :=: z2
  where d = 2000
