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
  data GoName = MkName Nat

  export
  Show GoName where
    show (MkName n) = show n

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
  data Declaration = Declare Kind GoName GoType

  %runElab derive "GoName" [Generic, DecEq, DE.Eq]
  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Declaration" [Generic, DecEq]

  ||| Set of declarations with unique names
  public export
  data Block
    = Nil
    | (::) Declaration Block

  public export
  isNewName : Block -> GoName -> Bool
  isNewName [] _ = True
  isNewName (Declare _ headName _ :: tail) newName =
    headName /= newName && isNewName tail newName

  public export
  data ByType : Block -> GoType -> Declaration -> Type where
    Here : forall kind, name, ty, rest.
           ByType (Declare kind name ty :: rest) ty (Declare kind name ty)

    There : forall decl, ty, head, rest.
            ByType rest ty decl ->
            ByType (head :: rest) ty decl


namespace Context
  public export
  record Context where
    constructor MkContext
    activeBlock : Block
    returns : GoTypes
    shouldReturn : Bool

  public export
  emptyContext : Context
  emptyContext = MkContext
    { activeBlock = [Declare Var (MkName 10) GoInt]
    , returns = [GoInt]
    , shouldReturn = True
    }

  -- public export
  -- data AddDeclaration : (ctxt : Context) ->
  --                       (decl : Declaration) ->
  --                       (newCtxt : Context) ->
  --                      Type where
  --   AddUnchecked : AddDeclaration ctxt decl (MkContext
  --                       (decl :: ctxt.activeBlock)
  --                       ctxt.returns
  --                       ctxt.shouldReturn)

  public export
  data AddDeclaration : (ctxt : Context) ->
                        (decl : Declaration) ->
                        (newCtxt : Context) ->
                        Type where
    AddUnchecked : AddDeclaration
                    (MkContext oldBlock rets sr)
                    decl
                    (MkContext (decl :: oldBlock) rets sr)

  public export
  AddDeclaration1 : Context -> Declaration -> Context
  AddDeclaration1 ctxt decl = { activeBlock $= (::) decl } ctxt


namespace Expr
  public export
  data Literal : (ty : GoType) -> Type where
    MkInt : Nat -> Literal GoInt
    MkBool : Bool -> Literal GoBool

  public export
  data PrefixOp : (argTy, resTy : GoType) -> Type where
    BoolNot : PrefixOp GoBool GoBool

  public export
  data InfixOp : (lhvTy, rhvTy, resTy : GoType) -> Type where
    IntAdd : InfixOp GoInt GoInt GoInt
    IntSub, IntMul : InfixOp GoInt GoInt GoInt
    BoolAnd, BoolOr : InfixOp GoBool GoBool GoBool

  public export
  data  BuiltinFunc : (args, rets : GoTypes) -> Type where
    Print : BuiltinFunc [GoInt] []

  public export
  data Expr : (ctxt : Context) -> (res : GoTypes) -> Type where
    GetLiteral : forall ctxt, resTy.
                 (lit : Literal resTy) ->
                 Expr ctxt [resTy]

    ApplyPrefix : forall ctxt, resTy, argTy.
                  (op : PrefixOp argTy resTy) ->
                  (arg : Expr ctxt [argTy]) ->
                  Expr ctxt [resTy]

    ApplyInfix : forall ctxt, resTy, lhvTy, rhvTy.
                 (op : InfixOp lhvTy rhvTy resTy) ->
                 (lhv : Expr ctxt [lhvTy]) ->
                 (rhv : Expr ctxt [rhvTy]) ->
                 Expr ctxt [resTy]

    CallBuiltin : forall ctxt, argTypes, retTypes.
                  (f : BuiltinFunc argTypes retTypes) ->
                  (args : Expr ctxt argTypes) ->
                  Expr ctxt retTypes

    -- CallNamed : forall ctxt, retTypes.
    --             (idx : Fin ctxt.depth) ->
    --             (isFunc : DefReturns ctxt.declarations idx retTypes) =>
    --             (params : Expr ctxt (ParamTypes ctxt.declarations idx {isFunc = isFunc})) ->
    --             Expr ctxt retTypes

    GetVar : forall ctxt, ty.
             (decl : Declaration) ->
             ByType ctxt.activeBlock ty decl =>
             Expr ctxt [ty]

    -- CallExpr : forall ctxt, argTypes, retTypes.
    --            (f : Expr ctxt [GoFunc argTypes retTypes]) ->
    --            (args : Expr ctxt argTypes) ->
    --            Expr ctxt retTypes


namespace Statement
  public export
  data AllowJustStop : Context -> Type where
    StopUnlessShouldReturn : AllowJustStop (MkContext { shouldReturn = True, _ })
    StopWhenReturnNone : AllowJustStop (MkContext { returns = [], _ })

  public export
  data AllowReturn : Context -> GoTypes -> Type where
    AllowReturnWhenShould : AllowReturn (MkContext _ types True) types

  public export
  data AllowInnerIf : (ctxt, ctxtThen, ctxtElse : Context) ->
                      Type where
    MkAllowInnerIf : AllowInnerIf (MkContext d r False)
                                  (MkContext d r _)
                                  (MkContext d r _)

  public export
  data ShouldReturn : Context -> Type where
    MkShouldReturn : ShouldReturn (MkContext _ _ True)

  %unbound_implicits off

  public export
  data Statement : (ctxt : Context) -> Type where
    DeclareVar : forall ctxt.
                 (name : GoName) ->
                 (new : So $ isNewName ctxt.activeBlock name) =>
                 (ty : GoType) ->
                 (initial : Expr ctxt [ty]) ->
                 {newCtxt : Context} ->
                 (AddDeclaration ctxt (Declare Var name ty) newCtxt) =>
                 (cont : Statement newCtxt) ->
                 Statement ctxt

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
