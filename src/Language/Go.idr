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

namespace Ty
  mutual
    public export
    record FuncTy where
      constructor MkFuncTy
      func_arg: Ty
      func_ret: Ty

    public export
    data Ty
      = Int'
      | Bool'
      | Func' FuncTy

  mutual
    Eq FuncTy where
      MkFuncTy a1 r1 == MkFuncTy a2 r2 = a1 == a2 && r1 == r2

    Eq Ty where
      Int' == Int' = True
      Bool' == Bool' = True
      Func' f1 == Func' f2 = assert_total $ f1 == f2
      _ == _ = False

  export
  Biinjective Ty.MkFuncTy where
    biinjective Refl = (Refl, Refl)

  export
  Injective Ty.Func' where
    injective Refl = Refl

  mutual
    %runElab derive "FuncTy" [Generic, DecEq]

    export
    DecEq Ty where
      decEq Int' Int' = Yes Refl
      decEq Bool' Bool' = Yes Refl
      decEq (Func' t1) (Func' t2) = decEqCong (assert_total decEq t1 t2)
      decEq Int' Bool' = No $ \case Refl impossible
      decEq Int' (Func' _) = No $ \case Refl impossible
      decEq Bool' Int' = No $ \case Refl impossible
      decEq Bool' (Func' _) = No $ \case Refl impossible
      decEq (Func' _) Int' = No $ \case Refl impossible
      decEq (Func' _) Bool' = No $ \case Refl impossible


namespace Def
  public export
  data Def : Type where
    DVar : (varTy : Ty) -> Def

  public export
  data Context : Type where
    Lin  : Context
    (:<) : Context -> Def -> Context

namespace Expr

  public export
  data Literal : Ty -> Type where
    MkInt : Nat -> Literal Int'
    MkBool : Bool -> Literal Bool'

  public export
  data Expr : (ctxt : Context) -> (res : Ty) -> Type where
    Const : (x : Literal ty) -> Expr ctxt ty

namespace Block
  mutual
    public export
    data AllowedInTnterIf : (retIf : Ty) ->
                            (retBranch : Ty) ->
                            Type where
      Con1 : AllowedInTnterIf ret ret
      Con2 : AllowedInTnterIf ret Bool'


    public export
    data Block : (ctxt : Context) ->
                 (ret : Ty) ->
                 Type where
      Return : Block ctxt ret

      InterIf : (test : Expr ctxt Bool') ->
                {retThen : Ty} ->
                {retElse : Ty} ->
                (th : Block ctxt retThen) ->
                (el : Block ctxt retElse) ->
                {allowThen : AllowedInTnterIf ret retThen} ->
                {allowElse : AllowedInTnterIf ret retElse} ->
                Block ctxt ret

export
genBlocks : Fuel -> (ctxt : Context) -> (ret : Ty) ->
                   Gen MaybeEmpty $ Block ctxt ret
