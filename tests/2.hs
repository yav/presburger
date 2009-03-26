import Data.Integer.Presburger

mytest1 = Exists $ \i -> Exists $ \j -> i :<: j :/\: j :=: 3
mytest2 = Exists $ \j -> j :=: 3 :/\: (Exists $ \i -> i :<: j)

main = print (check mytest1 == check mytest2)


