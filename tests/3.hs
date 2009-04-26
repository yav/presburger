import Data.Integer.Presburger

mytest5 =
  Not $ Forall $ \a ->
        Forall $ \b ->
        Forall $ \c ->
        Forall $ \d ->
        Forall $ \e ->
        Not $ a :=: 2 .* b
         :/\: b :=: c + 2
         :/\: d :=: 2 * c
         :/\: c :=: e + 1
         :/\: e :=: 1

mytest6 = 
        Exists $ \a ->
        Exists $ \b ->
        Exists $ \c ->
        Exists $ \d ->
        Exists $ \e ->
              a :=: 2 .* b
         :/\: b :=: c + 2
         :/\: d :=: 2 * c
         :/\: c :=: e + 1
         :/\: e :=: 1


main = print $ check mytest5
