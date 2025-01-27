module Language.Go

import Data.Fuel
import Data.Nat

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

public export
data Ty
  = Int'
  | Func'

export
DecEq Ty where
  decEq Int' Int' = Yes Refl
  decEq Func' Func' = Yes Refl
  decEq Int' Func' = No $ \case Refl impossible
  decEq Func' Int' = No $ \case Refl impossible


public export
data AllowedInTnterIf : (retIf : Ty) ->
                        (retBranch : Ty) ->
                        Type where
  AllowedSameRet : AllowedInTnterIf ret ret


public export
data Block : (ctxt : ()) ->
             (ret : Ty) ->
             Type where
  Return : Block ctxt ret

  InterIf : {allowThen : AllowedInTnterIf ret retThen} ->
            (th : Block ctxt retThen) ->
            Block ctxt ret
