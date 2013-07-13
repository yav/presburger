{-# LANGUAGE Safe #-}
module Data.Integer.Presburger.JList1 where

data JList a = One a | Two (JList a) (JList a)
                deriving Show

instance Functor JList where
  fmap f (One a)      = One (f a)
  fmap f (Two xs ys)  = Two (fmap f xs) (fmap f ys)

toList :: JList a -> [a]
toList xs = fold (:) xs []

fold :: (a -> b -> b) -> JList a -> b -> b
fold f (One x) r     = f x r
fold f (Two xs ys) r = fold f xs (fold f ys r)
