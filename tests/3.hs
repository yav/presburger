import Data.Integer.Presburger

mytest5 =
  Not $ forall $ \a b c d e ->
        Not $ a :=: 2 .* b
         :/\: b :=: c + 2
         :/\: d :=: 2 * c
         :/\: c :=: e + 1
         :/\: e :=: 1

mytest6 = exists $ \a b c d e ->
              a :=: 2 .* b
         :/\: b :=: c + 2
         :/\: d :=: 2 * c
         :/\: c :=: e + 1
         :/\: e :=: 1


main = do print $ check mytest5
          print $ check mytest6
