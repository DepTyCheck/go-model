module Language.Go

import Data.Fuel
import Data.Nat

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

public export
data T = A | B

DecEq T where
  decEq A A = Yes Refl
  decEq B B = Yes Refl
  decEq A B = No $ \case Refl impossible
  decEq B A = No $ \case Refl impossible

public export
data TEq : T -> T -> Type where
  Refl : TEq t t

public export
data S : () -> T -> Type where
  Em : S c r
  Con : S c t1 -> S c t2 -> TEq t1 t => S c t
