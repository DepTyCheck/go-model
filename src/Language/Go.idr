module Language.Go

import Data.Fuel
import Data.Nat

import Decidable.Equality

import Test.DepTyCheck.Gen

namespace Ty
  public export
  data Ty
    = Int'
    | Func'

  Eq Ty where
    Int' == Int' = True
    Func' == Func' = True
    _ == _ = False

  export
  DecEq Ty where
    decEq Int' Int' = Yes Refl
    decEq Func' Func' = Yes Refl
    decEq Int' Func' = No $ \case Refl impossible
    decEq Func' Int' = No $ \case Refl impossible


namespace Block
  mutual
    public export
    data AllowedInTnterIf : (retIf : Ty) ->
                            (retBranch : Ty) ->
                            Type where
      Con1 : AllowedInTnterIf ret ret
      Con2 : AllowedInTnterIf ret Int'


    public export
    data Block : (ctxt : ()) ->
                 (ret : Ty) ->
                 Type where
      Return : Block ctxt ret

      InterIf : {retThen : Ty} ->
                {retElse : Ty} ->
                (th : Block ctxt retThen) ->
                (el : Block ctxt retElse) ->
                {allowThen : AllowedInTnterIf ret retThen} ->
                {allowElse : AllowedInTnterIf ret retElse} ->
                Block ctxt ret

export
genBlocks : Fuel -> (ctxt : ()) -> (ret : Ty) ->
                   Gen MaybeEmpty $ Block ctxt ret
