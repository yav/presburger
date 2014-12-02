{-# LANGUAGE TemplateHaskell #-}
import Data.Integer.SAT

import Test.QuickCheck
import System.Exit

instance Arbitrary BoundType where
  arbitrary = elements [Lower, Upper]

withBounds :: Testable prop =>
  BoundType -> [(Positive Integer, Integer)] -> (Integer -> prop) -> Property
withBounds kind bs prop =
  counterexample (show (map toBound bs)) $
  case iPickBounded kind (map toBound bs) of
    Nothing -> property Discard
    Just n -> counterexample (show n) (property (prop n))
  where
    toBound (Positive c, t) = Bound c (tConst t)

prop_lower, prop_upper :: [(Positive Integer, Integer)] -> Property
prop_lower bs =
  withBounds Lower bs $ \n ->
    and [t <  c * n     | (Positive c, t) <- bs] &&
    or  [t >= c * (n-1) | (Positive c, t) <- bs]
prop_upper bs =
  withBounds Upper bs $ \n ->
    and [c * n     < t  | (Positive c, t) <- bs] &&
    or  [c * (n+1) >= t | (Positive c, t) <- bs]

-- This is so that the Template Haskell below can see the above properties.
$(return [])

main :: IO ()
main = do ok <- $(quickCheckAll)
          if ok then exitSuccess else exitFailure

