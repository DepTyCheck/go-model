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

namespace Ty
  mutual
    public export
    record FuncTy where
      constructor MkFuncTy
      arguments: Types
      returns: Types

    public export
    data Ty
      = Int'
      | Bool'
      | Func' FuncTy
      | Any'

    public export
    data Types : Type where
      Nil  : Types
      (::) : Ty -> Types -> Types

  public export
  length : Types -> Nat
  length Nil = Z
  length (_ :: sx) = S $ length sx

  public export %inline
  (.length) : Types -> Nat
  (.length) = length

  export
  asList : Types -> List Ty
  asList [] = []
  asList (t :: ts) = t :: asList ts

  export
  Biinjective Ty.(::) where
    biinjective Refl = (Refl, Refl)

  export
  Injective Ty.Func' where
    injective Refl = Refl

  export
  Biinjective Ty.MkFuncTy where
    biinjective Refl = (Refl, Refl)

  mutual
    %runElab derive "Ty" [Generic, DecEq]
    -- export
    -- DecEq Ty where
    --   decEq Int' Int' = Yes Refl
    --   decEq Bool' Bool' = Yes Refl
    --   decEq (Func' t1 r1) (Func' t2 r2) = decEqCong2 (assert_total decEq t1 t2) (assert_total decEq r1 r2)
    --   decEq Any' Any' = Yes Refl
    --   decEq Int' Bool' = No $ \case Refl impossible
    --   decEq Int' (Func' _ _) = No $ \case Refl impossible
    --   decEq Int' Any' = No $ \case Refl impossible
    --   decEq Bool' Int' = No $ \case Refl impossible
    --   decEq Bool' (Func' _ _) = No $ \case Refl impossible
    --   decEq Bool' Any' = No $ \case Refl impossible
    --   decEq (Func' _ _) Int' = No $ \case Refl impossible
    --   decEq (Func' _ _) Bool' = No $ \case Refl impossible
    --   decEq (Func' _ _) Any' = No $ \case Refl impossible
    --   decEq Any' Int' = No $ \case Refl impossible
    --   decEq Any' Bool' = No $ \case Refl impossible
    --   decEq Any' (Func' _ _) = No $ \case Refl impossible

    export
    DecEq FuncTy where
      decEq (MkFuncTy a1 r1) (MkFuncTy a2 r2) =
        assert_total decEqCong2 (decEq a1 a2) (decEq r1 r2)

    export
    DecEq Types where
      decEq Nil Nil = Yes Refl
      decEq Nil (_ :: _) = No $ \case Refl impossible
      decEq (_ :: _) Nil = No $ \case Refl impossible
      decEq (xs :: x) (xs' :: x') = assert_total decEqCong2 (decEq xs xs') (decEq x x')

  public export
  data Assignable : (lhv : Types) -> (rhv : Types) -> Type where
    AssignEmpty : Assignable [] []

    AssignSame : forall t, ts1, ts2.
                 Assignable ts1 ts2 =>
                 Assignable (t :: ts1) (t :: ts2)

    AssignToAny : forall t, ts1, ts2.
                  Assignable ts1 ts2 =>
                  Assignable (Any' :: ts1) (t :: ts2)


namespace Definition
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
  record Definition where
    constructor Define
    defKind  : Kind
    defTy : Ty
    defName : Nat

  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Definition" [Generic, DecEq]

  public export
  data Definitions : (size : Nat) -> Type where
    Nil  : Definitions Z
    (::) : Definition -> Definitions n -> Definitions (S n)

  export
  dig : (defs : Definitions n) -> (idx: Fin n) -> Definition
  dig (x :: _) FZ = x
  dig (_ :: ds) (FS i) = dig ds i

  public export
  data DefTypeIs : (defs : Definitions n) ->
                   (idx : Fin n) ->
                   (ty : Ty) ->
                   Type where
    Here'  : DefTypeIs (Define _ ty _ :: _) FZ ty
    There' : DefTypeIs rest idx ty ->
             DefTypeIs (_ :: rest) (FS idx) ty

  public export
  data DefReturns : (defs : Definitions n) ->
                    (idx : Fin n) ->
                    (retTypes : Types) ->
                    Type where
    Here''  : DefReturns (Define _ (Func' $ MkFuncTy _ retTypes) _ :: _) FZ retTypes
    There'' : DefReturns rest idx retTypes ->
              DefReturns (_ :: rest) (FS idx) retTypes

  public export
  ParamTypes : forall n, retTypes.
               (defs : Definitions n) ->
               (idx : Fin n) ->
               (isFunc : DefReturns defs idx retTypes) =>
               Types
  ParamTypes (_ :: rest) (FS next) {isFunc = There'' x} =
    ParamTypes rest next {isFunc = x}
  ParamTypes (Define _ (Func' $ MkFuncTy parTypes retTypes) _ :: _) FZ {isFunc = Here''} =
    parTypes


namespace Context
  public export
  record Context where
    constructor MkContext
    depth : Nat
    definitions : Definitions depth
    returns : Types
    shouldReturn : Bool

  public export
  emptyContext : Context
  emptyContext = MkContext
    { depth = _
    , definitions = []
    , returns = [Int']
    , shouldReturn = True
    }

  public export
  data AddDefinition : (ctxt : Context) ->
                       (kind : Kind) ->
                       (ty : Ty) ->
                       (newCtxt : Context) ->
                       Type where
    MkAddDefinition : AddDefinition ctxt kind newTy (MkContext
                        (S ctxt.depth)
                        (Define kind newTy ctxt.depth :: ctxt.definitions)
                        ctxt.returns
                        ctxt.shouldReturn)

namespace Expr
  mutual
    public export
    data SpecialForm : (ctxt : Context) -> (res : Types) -> Type where
      Print : (arg : Expr ctxt _) -> SpecialForm ctxt []
      IntAdd : (lhv, rhv : Expr ctxt [Int']) -> SpecialForm ctxt [Int']
      IntSub, IntMul : (lhv, rhv : Expr ctxt [Int']) -> SpecialForm ctxt [Int']
      BoolAnd, BoolOr : (lhv, rhv : Expr ctxt [Bool']) -> SpecialForm ctxt [Bool']
      BoolNot : (arg : Expr ctxt [Bool']) -> SpecialForm ctxt [Bool']

    public export
    data Expr : (ctxt : Context) -> (res : Types) -> Type where
      CallNamed : forall ctxt, retTypes.
                  (idx : Fin ctxt.depth) ->
                  (isFunc : DefReturns ctxt.definitions idx retTypes) =>
                  (params : Expr ctxt (ParamTypes ctxt.definitions idx {isFunc = isFunc})) ->
                  Expr ctxt retTypes

      IntLiteral  : (x : Nat) -> Expr ctxt [Int']
      BoolLiteral : (x : Bool) -> Expr ctxt [Bool']

      GetVar : (idx : Fin ctxt.depth) ->
               DefTypeIs ctxt.definitions idx ty =>
               Expr ctxt [ty]

      SpecForm : SpecialForm ctxt res -> Expr ctxt res

      -- CallExpr : forall ctxt, argTypes, retTypes.
      --            (f : Expr ctxt [Func' argTypes retTypes]) ->
      --            (args : Expr ctxt argTypes) ->
      --            Expr ctxt retTypes


namespace Block
  public export
  data AllowJustStop : Context -> Type where
    StopUnlessShouldReturn : AllowJustStop (MkContext _ _ _ False)
    StopWhenReturnNone : AllowJustStop (MkContext _ _ [] _)

  public export
  data AllowReturn : Context -> Types -> Type where
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
  data Block : (ctxt : Context) -> Type where

    JustStop : forall ctxt.
               AllowJustStop ctxt =>
               Block ctxt

    Return : forall ctxt, rets.
             AllowReturn ctxt rets =>
             (res : Expr ctxt rets) ->
             Block ctxt

    VoidExpr : forall ctxt.
               (expr : Expr ctxt []) ->
               (cont : Block ctxt) ->
               Block ctxt

    InnerIf : forall ctxt.
              (test : Expr ctxt [Bool']) ->
              {ctxtThen, ctxtElse : Context} ->
              AllowInnerIf ctxt ctxtThen ctxtElse =>
              (th : Block ctxtThen) ->
              (el : Block ctxtElse) ->
              (cont : Block ctxt) ->
              Block ctxt

    TermIf : forall ctxt.
             ShouldReturn ctxt =>
             (test : Expr ctxt [Bool']) ->
             (th : Block ctxt) ->
             (el : Block ctxt) ->
             Block ctxt

    InitVar : forall ctxt.
              (newTy : Ty) ->
              (initVal : Expr ctxt [newTy]) ->
              {newCtxt : Context} ->
              (pr : AddDefinition ctxt Var newTy newCtxt) =>
              (cont : Block newCtxt) ->
              Block ctxt

  %unbound_implicits on

  export
  isEmpty : Block _ -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genBlocks : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Block ctxt

export
genExprs : Fuel -> (ctxt : Context) -> (rets : Types) ->
                   Gen MaybeEmpty $ Expr ctxt rets
