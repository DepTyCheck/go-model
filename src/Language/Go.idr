module Language.Go

import Data.Fuel
import Data.Nat

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

public export
data Ty = A | B

export
DecEq Ty where
  decEq A A = Yes Refl
  decEq B B = Yes Refl
  decEq A B = No $ \case Refl impossible
  decEq B A = No $ \case Refl impossible

public export
data TEq : Ty -> Ty -> Type where
  Refl : TEq t t

public export
data Block : () -> Ty -> Type where
  Ret : Block c r
  Cons : {eq : TEq t1 t2} -> (x : Block c t1) -> Block c t2
