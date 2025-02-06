module Language.Go.Derived

import Language.Go

import Deriving.DepTyCheck.Gen

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15


export
gen : Fuel -> (c : ()) -> (r : T) -> Gen MaybeEmpty $ S c r
gen = deriveGen
