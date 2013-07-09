{-# LANGUAGE Safe #-}
module JList1 where

data JList a = One a | Two (JList a) (JList a)
                deriving Show

instance Functor JList where
  fmap f (One a)      = One (f a)
  fmap f (Two xs ys)  = Two (fmap f xs) (fmap f ys)

toList :: JList a -> [a]
toList xs = go xs []
  where go (One a) as     = a : as
        go (Two as bs) cs = go as (go bs cs)


fold :: (a -> a -> a) -> JList a -> a
fold _ (One x)      = x
fold f (Two xs ys)  = f (fold f xs) (fold f ys)
