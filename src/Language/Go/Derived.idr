module Language.Go.Derived

import Language.Go

import Deriving.DepTyCheck.Gen

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15


export
gen : Fuel -> (r : Ty) -> Gen MaybeEmpty $ Block r
gen = deriveGen
