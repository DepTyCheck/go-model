module Language.Go

import Data.Fuel
import Data.Nat
import Data.Fin
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE

import Generics.Derive

import Test.DepTyCheck.Gen

%language ElabReflection

namespace GoType
  mutual
    public export
    record FuncTy where
      constructor MkFuncTy
      arguments: GoTypes
      returns: GoTypes

    public export
    data GoType
      = GoInt
      | GoBool
      | GoFunc FuncTy
      | GoAny

    public export
    data GoTypes : Type where
      Nil  : GoTypes
      (::) : GoType -> GoTypes -> GoTypes

  public export
  length : GoTypes -> Nat
  length Nil = Z
  length (_ :: sx) = S $ length sx

  public export %inline
  (.length) : GoTypes -> Nat
  (.length) = length

  export
  asList : GoTypes -> List GoType
  asList [] = []
  asList (t :: ts) = t :: asList ts

  export
  Biinjective GoType.(::) where
    biinjective Refl = (Refl, Refl)

  export
  Injective GoType.GoFunc where
    injective Refl = Refl

  export
  Biinjective GoType.MkFuncTy where
    biinjective Refl = (Refl, Refl)

  mutual
    %runElab derive "GoType" [Generic, DecEq]

    export
    DecEq FuncTy where
      decEq (MkFuncTy a1 r1) (MkFuncTy a2 r2) =
        assert_total decEqCong2 (decEq a1 a2) (decEq r1 r2)

    export
    DecEq GoTypes where
      decEq Nil Nil = Yes Refl
      decEq Nil (_ :: _) = No $ \case Refl impossible
      decEq (_ :: _) Nil = No $ \case Refl impossible
      decEq (xs :: x) (xs' :: x') = assert_total decEqCong2 (decEq xs xs') (decEq x x')

  public export
  data Assignable : (lhv : GoTypes) -> (rhv : GoTypes) -> Type where
    AssignEmpty : Assignable [] []

    AssignSame : forall t, ts1, ts2.
                 Assignable ts1 ts2 =>
                 Assignable (t :: ts1) (t :: ts2)

    AssignToAny : forall t, ts1, ts2.
                  Assignable ts1 ts2 =>
                  Assignable (GoAny :: ts1) (t :: ts2)


namespace Declaration
  public export
  data Kind
    = Var
    | Const
    | Func

  export
  Show Kind where
    show Var = "v"
    show Const = "c"
    show Func = "f"

  public export
  record Declaration where
    constructor Define
    declKind  : Kind
    declTy : GoType
    declName : Nat

  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Declaration" [Generic, DecEq]

  public export
  data Declarations : (size : Nat) -> Type where
    Nil  : Declarations Z
    (::) : Declaration -> Declarations n -> Declarations (S n)

  export
  dig : (decls : Declarations n) -> (idx: Fin n) -> Declaration
  dig (x :: _) FZ = x
  dig (_ :: ds) (FS i) = dig ds i

  public export
  data DefTypeIs : (decls : Declarations n) ->
                   (idx : Fin n) ->
                   (ty : GoType) ->
                   Type where
    Here'  : DefTypeIs (Define _ ty _ :: _) FZ ty
    There' : DefTypeIs rest idx ty ->
             DefTypeIs (_ :: rest) (FS idx) ty

  public export
  data DefReturns : (decls : Declarations n) ->
                    (idx : Fin n) ->
                    (retTypes : GoTypes) ->
                    Type where
    Here''  : DefReturns (Define _ (GoFunc $ MkFuncTy _ retTypes) _ :: _) FZ retTypes
    There'' : DefReturns rest idx retTypes ->
              DefReturns (_ :: rest) (FS idx) retTypes

  public export
  ParamTypes : forall n, retTypes.
               (decls : Declarations n) ->
               (idx : Fin n) ->
               (isFunc : DefReturns decls idx retTypes) =>
               GoTypes
  ParamTypes (_ :: rest) (FS next) {isFunc = There'' x} =
    ParamTypes rest next {isFunc = x}
  ParamTypes (Define _ (GoFunc $ MkFuncTy parTypes retTypes) _ :: _) FZ {isFunc = Here''} =
    parTypes


namespace Context
  public export
  record Context where
    constructor MkContext
    depth : Nat
    declarations : Declarations depth
    returns : GoTypes
    shouldReturn : Bool

  public export
  emptyContext : Context
  emptyContext = MkContext
    { depth = _
    , declarations = []
    , returns = [GoInt]
    , shouldReturn = True
    }

  public export
  data AddDeclaration : (ctxt : Context) ->
                       (kind : Kind) ->
                       (ty : GoType) ->
                       (newCtxt : Context) ->
                       Type where
    MkAddDeclaration : AddDeclaration ctxt kind newTy (MkContext
                        (S ctxt.depth)
                        (Define kind newTy ctxt.depth :: ctxt.declarations)
                        ctxt.returns
                        ctxt.shouldReturn)

namespace Expr
  mutual
    public export
    data SpecialForm : (ctxt : Context) -> (res : GoTypes) -> Type where
      Print : (arg : Expr ctxt _) -> SpecialForm ctxt []
      IntAdd : (lhv, rhv : Expr ctxt [GoInt]) -> SpecialForm ctxt [GoInt]
      -- IntSub, IntMul : (lhv, rhv : Expr ctxt [GoInt]) -> SpecialForm ctxt [GoInt]
      -- BoolAnd, BoolOr : (lhv, rhv : Expr ctxt [GoBool]) -> SpecialForm ctxt [GoBool]
      -- BoolNot : (arg : Expr ctxt [GoBool]) -> SpecialForm ctxt [GoBool]

    public export
    data Expr : (ctxt : Context) -> (res : GoTypes) -> Type where
      CallNamed : forall ctxt, retTypes.
                  (idx : Fin ctxt.depth) ->
                  (isFunc : DefReturns ctxt.declarations idx retTypes) =>
                  (params : Expr ctxt (ParamTypes ctxt.declarations idx {isFunc = isFunc})) ->
                  Expr ctxt retTypes

      IntLiteral  : (x : Nat) -> Expr ctxt [GoInt]
      BoolLiteral : (x : Bool) -> Expr ctxt [GoBool]

      GetVar : (idx : Fin ctxt.depth) ->
               DefTypeIs ctxt.declarations idx ty =>
               Expr ctxt [ty]

      SpecForm : SpecialForm ctxt res -> Expr ctxt res

      -- CallExpr : forall ctxt, argTypes, retTypes.
      --            (f : Expr ctxt [GoFunc argTypes retTypes]) ->
      --            (args : Expr ctxt argTypes) ->
      --            Expr ctxt retTypes


namespace Statement
  public export
  data AllowJustStop : Context -> Type where
    StopUnlessShouldReturn : AllowJustStop (MkContext _ _ _ False)
    StopWhenReturnNone : AllowJustStop (MkContext _ _ [] _)

  public export
  data AllowReturn : Context -> GoTypes -> Type where
    AllowReturnWhenShould : AllowReturn (MkContext _ _ types True) types

  public export
  data AllowInnerIf : (ctxt, ctxtThen, ctxtElse : Context) ->
                      Type where
    MkAllowInnerIf : AllowInnerIf (MkContext n d r False)
                                  (MkContext n d r _)
                                  (MkContext n d r _)

  public export
  data ShouldReturn : Context -> Type where
    MkShouldReturn : ShouldReturn (MkContext _ _ _ True)

  %unbound_implicits off

  public export
  data Statement : (ctxt : Context) -> Type where

    JustStop : forall ctxt.
               AllowJustStop ctxt =>
               Statement ctxt

    Return : forall ctxt, rets.
             AllowReturn ctxt rets =>
             (res : Expr ctxt rets) ->
             Statement ctxt

    VoidExpr : forall ctxt.
               (expr : Expr ctxt []) ->
               (cont : Statement ctxt) ->
               Statement ctxt

    InnerIf : forall ctxt.
              (test : Expr ctxt [GoBool]) ->
              {ctxtThen, ctxtElse : Context} ->
              AllowInnerIf ctxt ctxtThen ctxtElse =>
              (th : Statement ctxtThen) ->
              (el : Statement ctxtElse) ->
              (cont : Statement ctxt) ->
              Statement ctxt

    TermIf : forall ctxt.
             ShouldReturn ctxt =>
             (test : Expr ctxt [GoBool]) ->
             (th : Statement ctxt) ->
             (el : Statement ctxt) ->
             Statement ctxt

    InitVar : forall ctxt.
              (newTy : GoType) ->
              (initVal : Expr ctxt [newTy]) ->
              {newCtxt : Context} ->
              (pr : AddDeclaration ctxt Var newTy newCtxt) =>
              (cont : Statement newCtxt) ->
              Statement ctxt

  %unbound_implicits on

  export
  isEmpty : Statement _ -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs : Fuel -> (ctxt : Context) -> (rets : GoTypes) ->
                   Gen MaybeEmpty $ Expr ctxt rets
