module Language.Go.Derived

import Language.Go

import Deriving.DepTyCheck.Gen

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15


export
genBlocks : Fuel -> (ctxt : ()) -> (ret : Ty) ->
                   Gen MaybeEmpty $ Block ctxt ret
genBlocks = deriveGen
