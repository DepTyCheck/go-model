module Language.Go

import Data.Fuel
import Data.Nat

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

public export
data Ty = A | B

public export
data TEq : Ty -> Ty -> Type where
  Refl : TEq t t

public export
data Block : Ty -> Type where
  Em : Block r
  Con : Block t1 -> TEq t1 t2 => Block t2
