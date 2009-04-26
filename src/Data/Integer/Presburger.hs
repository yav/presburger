{-| This module implements Cooper's algorithm for deciding
    first order formulas over integers with addition.

Based on the paper:
 * author: D.C.Cooper
 * title:  "Theorem Proving in Arithmetic without Multiplication"
 * year:   1972
-}
module Data.Integer.Presburger (module X) where
  
import Data.Integer.Presburger.HOAS as X