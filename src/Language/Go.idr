module Language.Go

import Data.Fuel
import Data.Nat
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE

import Generics.Derive

import Test.DepTyCheck.Gen

import Utils.MkSnocList

%language ElabReflection


public export
data Ty
  = NoValue
  | Int'
  | Bool'
  | Error'
  | Chan'

%runElab derive "Ty" [Generic, DE.Eq, DecEq]

public export
data Literal : Ty -> Type where
  MkInt : Int -> Literal Int'
  MkBool : Bool -> Literal Bool'

namespace SnocListTy

  public export
  data SnocListTy : Type where
    Lin  : SnocListTy
    (:<) : SnocListTy -> Ty -> SnocListTy

  %runElab derive "SnocListTy" [DE.Eq]

  public export
  snocListTyToList : SnocListTy -> List Ty
  snocListTyToList Lin = []
  snocListTyToList (xs :< x) = (snocListTyToList xs) ++ [x]

  public export
  length : SnocListTy -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : SnocListTy -> Nat
  (.length) = length

  export
  Biinjective SnocListTy.(:<) where
    biinjective Refl = (Refl, Refl)

  export
  DecEq SnocListTy where
    decEq [<] [<] = Yes Refl
    decEq (sx :< x) (sx' :< x') = decEqCong2 (decEq sx sx') (decEq x x')
    decEq [<] (_:<_) = No $ \case Refl impossible
    decEq (_:<_) [<] = No $ \case Refl impossible
