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
    data MaybeTy
      = Nothing
      | Just Ty

    public export
    data Types : Type where
      Lin  : Types
      (:<) : Types -> Ty -> Types

  mutual
    %runElab derive "FuncTy" [DE.Eq]
    %runElab derive "Ty" [DE.Eq]
    %runElab derive "MaybeTy" [DE.Eq]

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

  mutual
    %runElab derive "FuncTy" [Generic, DecEq]
    %runElab derive "Ty" [Generic, DecEq]
    %runElab derive "MaybeTy" [Generic, DecEq]

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

  public export
  data IndexIn : Context -> Type where
    Here  : IndexIn $ sx :< x
    There : IndexIn sx -> IndexIn $ sx :< x

  public export
  index : (sx : Context) -> IndexIn sx -> Def
  index (_ :<x) Here      = x
  index (sx:<_) (There i) = index sx i

  public export
  length : Context -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : Context -> Nat
  (.length) = length

  public export
  data AtIndex : {sx : Context} -> (idx : IndexIn sx) -> Def -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = sx :< sig} Here sig
    There' : AtIndex {sx} i sig -> AtIndex {sx = sx :< x} (There i) sig

namespace Expr

  public export
  data Literal : Ty -> Type where
    MkInt : Nat -> Literal Int'
    MkBool : Bool -> Literal Bool'

  export
  Show (Literal ty) where
    show (MkInt x) = show x
    show (MkBool True) = "true"
    show (MkBool False) = "false"

  public export
  data Expr : (ctxt : Context) -> (res : Types) -> Type where
    Const : (x : Literal ty) -> Expr ctxt [<ty]

namespace Block
  public export
  record BlockOpts where
    constructor MkBlockOpts
    mustTerm : Bool

  public export
  data Block : (ctxt : Context) ->
               (cont : Types) ->
               (bo : BlockOpts) ->
               Type where
    End : Block ctxt cont (MkBlockOpts False)

    Ret : (res : Expr ctxt cont) -> Block ctxt cont bo

    SimpleIf : (test : Expr ctxt [<Bool']) ->
               (th, el : Block ctxt cont (MkBlockOpts False))->
               (next : Block ctxt cont bo) ->
               Block ctxt cont bo

  export
  isNop : Block _ _ _ -> Bool
  isNop End = True
  isNop _ = False

export
genBlocks : Fuel -> (ctxt : Context) -> (cont : Types) -> (bo : BlockOpts) ->
                   Gen MaybeEmpty $ Block ctxt cont bo
