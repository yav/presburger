module Data.Integer.Presburger.Utils
  ( module Data.Integer.Presburger.Utils
  , module PP
  ) where

import Text.PrettyPrint.HughesPJ as PP




lcms :: Integral a => [a] -> a
lcms xs = foldr lcm 1 xs


groupEither :: [Either a b] -> ([a],[b])
groupEither xs = foldr cons ([],[]) xs
  where cons (Left a)  (as,bs) = (a:as,bs)
        cons (Right b) (as,bs) = (as,b:bs)

mapEither :: (a -> Either x y) -> [a] -> ([x],[y])
mapEither f xs = groupEither (map f xs)


-- | let (p,q,r) = extended_gcd x y
--   in (x * p + y * q = r)  &&  (gcd x y = r)
extended_gcd :: Integral a => a -> a -> (a,a,a)
extended_gcd arg1 arg2 = loop arg1 arg2 0 1 1 0
  where loop a b x lastx y lasty
          | b /= 0    = let (q,b') = divMod a b
                            x'     = lastx - q * x
                            y'     = lasty - q * y
                        in x' `seq` y' `seq` loop b b' x' x y' y
          | otherwise = (lastx,lasty,a)


-- We define: "d | a" as "exists y. d * y = a"
divides :: Integral a => a -> a -> Bool
0 `divides` 0 = True
0 `divides` _ = False
x `divides` y = mod y x == 0


class PP a where
  pp :: a -> Doc

