import Data.Integer.Presburger

iff f1 f2 = (f1 :=>: f2) :/\: (f2 :=>: f1)
div1 k t  = Exists $ \x -> k .* x :=: t
test k    = Forall $ \x -> div1 k x `iff` (k :| x)



