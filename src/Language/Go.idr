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
      args : Types
      rets : Types

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
    %runElab derive "Ty" [Generic, DecEq]
    -- export
    -- DecEq FuncTy where
    --   decEq (MkFuncTy p1 r1) (MkFuncTy p2 r2) = decEqCong2 (decEq p1 p2) (decEq r1 r2)

    -- export
    -- DecEq Ty where
    --   decEq Int' Int' = Yes Refl
    --   decEq Bool' Bool' = Yes Refl
    --   decEq (Func' t1) (Func' t2) = decEqCong (assert_total decEq t1 t2)
    --   decEq Int' Bool' = No $ \case Refl impossible
    --   decEq Int' (Func' _) = No $ \case Refl impossible
    --   decEq Bool' Int' = No $ \case Refl impossible
    --   decEq Bool' (Func' _) = No $ \case Refl impossible
    --   decEq (Func' _) Int' = No $ \case Refl impossible
    --   decEq (Func' _) Bool' = No $ \case Refl impossible

    export
    DecEq Types where
      decEq Lin Lin = Yes Refl
      decEq Lin (_ :< _) = No $ \case Refl impossible
      decEq (_ :< _) Lin = No $ \case Refl impossible
      decEq (xs :< x) (xs' :< x') = decEqCong2 (decEq xs xs') (decEq x x')


namespace Definition
  public export
  data Definition : Type where
    DVar : (varTy : Ty) -> Definition

  public export
  data Definitions : Type where
    Lin  : Definitions
    (:<) : Definitions -> Definition -> Definitions

  public export
  data IndexIn : Definitions -> Type where
    Here  : IndexIn $ sx :< x
    There : IndexIn sx -> IndexIn $ sx :< x

  public export
  index : (sx : Definitions) -> IndexIn sx -> Definition
  index (_ :<x) Here      = x
  index (sx:<_) (There i) = index sx i

  public export
  length : Definitions -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : Definitions -> Nat
  (.length) = length

  public export
  data AtIndex : {sx : Definitions} -> (idx : IndexIn sx) -> Definition -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = sx :< sig} Here sig
    There' : AtIndex {sx} i sig -> AtIndex {sx = sx :< x} (There i) sig


namespace Context
  public export
  record Context where
    constructor MkContext
    definitions : Definitions
    returnType : Types


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
  data AllowJustStop : (ctxt : Context) ->
                       (isTerminating : Bool) ->
                       Type where
    StopWhenNonTerminating : AllowJustStop _ False
    StopWhenReturnNone : AllowJustStop (MkContext _ [<]) isTerminating


  public export
  data AllowInnerIf : (isTerminatingThen : Bool) ->
                      (isTerminatingElse : Bool) ->
                      Type where
    InnerIfCC : AllowInnerIf False False
    InnerIfCT : AllowInnerIf False True
    InnerIfTC : AllowInnerIf True False


  mutual
    public export
    data Block : (ctxt : Context) ->
                 (isReturning : Bool) ->
                 Type where

      JustStop : {_ : AllowJustStop ctxt isTerminating} ->
                 Block ctxt isTerminating

      Return : (res : Expr (MkContext defs ret) ret) ->
               Block (MkContext defs ret) True

      InnerIf : (test : Expr ctxt [<Bool']) ->
                {_ : AllowInnerIf isTerminatingThen isTerminatingElse} ->
                (th : Block ctxt isTerminatingThen) ->
                (el : Block ctxt isTerminatingElse) ->
                (cont : Block ctxt isTerminating) ->
                Block ctxt isTerminating

      TermIf : (test : Expr ctxt [<Bool']) ->
               (th : Block ctxt True) ->
               (el : Block ctxt True) ->
               Block ctxt True

  export
  isEmpty : Block _ _ -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genBlocks : Fuel -> (ctxt : Context) -> (isTerminating : Bool) ->
            Gen MaybeEmpty $ Block ctxt isTerminating
