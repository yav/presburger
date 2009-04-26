module Data.Integer.Presburger.Notation
  ( check, Formula
  , module Data.Integer.Presburger.Notation
  ) where

import Data.Integer.Presburger.Form
import Prelude hiding ((<),(<=),(==),(/=),(>),(>=), not, (&&), (||))
import qualified Prelude as P

type Formula = Form (Prop PosP)

infixr 2 ||
infixr 3 &&
infix 4 <, <=, ==, >, >=, /=



(&&), (||) :: Formula -> Formula -> Formula
f1 && f2 = Node And f1 f2
f1 || f2 = Node Or f1 f2

(<) :: Term -> Term -> Formula
t1 < t2 = Leaf $ Prop False $ Bin LessThan t1 t2

(<=) :: Term -> Term -> Formula
t1 <= t2 = Leaf $ Prop False $ Bin LessThanEqual t1 t2

(==) :: Term -> Term -> Formula
t1 == t2 = Leaf $ Prop False $ Bin Equal t1 t2

exists :: Name -> Formula -> Formula
exists x f = ex_step x f

not :: Formula -> Formula
not = neg

(>) :: Term -> Term -> Formula
t1 > t2 = not (t1 <= t2)

(>=) :: Term -> Term -> Formula
t1 >= t2 = not (t1 < t2)

(/=) :: Term -> Term -> Formula
t1 /= t2  = not (t1 == t2)

forall :: Name -> Formula -> Formula
forall x f = not (exists x (not f))
