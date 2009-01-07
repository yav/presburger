module Euclid where

-- | let (p,q,r) = extended_gcd x y
--   in (x * p + y * q = r)  &&  (gcd x y = r)
extended_gcd :: Integral a => a -> a -> (a,a,a)
extended_gcd a b = loop a b 0 1 1 0
  where loop a b x lastx y lasty
          | b /= 0    = let (q,b') = divMod a b
                            x'     = lastx - q * x
                            y'     = lasty - q * y
                        in x' `seq` y' `seq` loop b b' x' x y' y
          | otherwise = (lastx,lasty,a)


