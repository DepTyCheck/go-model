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
      args: Types
      rets: Types

    public export
    data Ty
      = Int'
      | Bool'
      | Func' FuncTy

    public export
    data Types : Type where
      Lin  : Types
      (:<) : Types -> Ty -> Types

  mutual
    %runElab derive "FuncTy" [DE.Eq]
    %runElab derive "Ty" [DE.Eq]

    public export
    Eq Types where
      (==) Lin Lin = True
      (==) (xs :< x) (xs' :< x') = assert_total $ xs == xs' && x == x'
      (==) _ _ = False

  public export
  snocListTyToList : Types -> List Ty
  snocListTyToList Lin = []
  snocListTyToList (xs :< x) = (snocListTyToList xs) ++ [x]

  public export
  length : Types -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : Types -> Nat
  (.length) = length

  export
  Biinjective Ty.MkFuncTy where
    biinjective Refl = (Refl, Refl)

  export
  Biinjective Ty.(:<) where
    biinjective Refl = (Refl, Refl)

  export
  Injective Ty.Func' where
    injective Refl = Refl

  mutual
    %runElab derive "FuncTy" [Generic, DecEq]
    -- %runElab derive "Ty" [Generic, DecEq]
    -- export
    -- DecEq FuncTy where
    --   decEq (MkFuncTy p1 r1) (MkFuncTy p2 r2) = decEqCong2 (decEq p1 p2) (decEq r1 r2)

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

    export
    DecEq Types where
      decEq Lin Lin = Yes Refl
      decEq Lin (_ :< _) = No $ \case Refl impossible
      decEq (_ :< _) Lin = No $ \case Refl impossible
      decEq (xs :< x) (xs' :< x') = decEqCong2 (decEq xs xs') (decEq x x')


namespace Def
  public export
  data Def : Type where
    DVar : (varTy : Ty) -> Def

  public export
  data Context : Type where
    Lin  : Context
    (:<) : Context -> Def -> Context

  -- public export
  -- data IndexIn : Context -> Type where
  --   Here  : IndexIn $ sx :< x
  --   There : IndexIn sx -> IndexIn $ sx :< x

  -- public export
  -- index : (sx : Context) -> IndexIn sx -> Def
  -- index (_ :<x) Here      = x
  -- index (sx:<_) (There i) = index sx i

  -- public export
  -- length : Context -> Nat
  -- length Lin = Z
  -- length (sx :< _) = S $ length sx

  -- public export %inline
  -- (.length) : Context -> Nat
  -- (.length) = length

  -- public export
  -- data AtIndex : {sx : Context} -> (idx : IndexIn sx) -> Def -> Type where
  --   [search sx idx]
  --   Here'  : AtIndex {sx = sx :< sig} Here sig
  --   There' : AtIndex {sx} i sig -> AtIndex {sx = sx :< x} (There i) sig

namespace Expr

  public export
  data Literal : Ty -> Type where
    MkInt : Nat -> Literal Int'
    MkBool : Bool -> Literal Bool'

  public export
  data Expr : (ctxt : Context) -> (res : Types) -> Type where
    Const : (x : Literal ty) -> Expr ctxt [<ty]

namespace Block
  mutual
    public export
    data AllowedInTnterIf : (retIf : Types) ->
                            (retBranch : Types) ->
                            Type where
      RetSameAllowedInInterIf : AllowedInTnterIf ret ret
      NoRetAllowedInInterIf : AllowedInTnterIf ret [<]


    public export
    data Block : (ctxt : Context) ->
                 (ret : Types) ->
                 Type where
      Return : Block ctxt ret

      InterIf : (test : Expr ctxt [<Bool']) ->
                {retThen : Types} ->
                {retElse : Types} ->
                (th : Block ctxt retThen) ->
                (el : Block ctxt retElse) ->
                {allowThen : AllowedInTnterIf ret retThen} ->
                {allowElse : AllowedInTnterIf ret retElse} ->
                Block ctxt ret

export
genBlocks : Fuel -> (ctxt : Context) -> (ret : Types) ->
                   Gen MaybeEmpty $ Block ctxt ret
