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
%unbound_implicits on

namespace GoType
  mutual
    public export
    record FuncTy where
      constructor MkFuncTy
      arguments: GoTypes
      returns: GoTypes

    ||| Types from Go Language
    |||
    ||| GoInt <-> int
    ||| GoAny <-> interface {}
    ||| Note: GoAny can slow down generation if there are any non constructible types
    public export
    data GoType
      = GoInt
      | GoBool
      | GoFunc FuncTy
      -- @WHEN ASSIGNABLE_ANY
      -- @ | GoAny
      -- @END ASSIGNABLE_ANY

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

namespace Assignable
  public export
  data Assignable1 : (lhv, rhv : GoType) -> Type where
    AssignSame : forall t. Assignable1 t t

    -- @WHEN ASSIGNABLE_ANY
    -- @ AssignToAny :  forall t. Assignable1 GoAny t
    -- @END ASSIGNABLE_ANY

  public export
  data Assignable : (lhv, rhv : GoTypes) -> Type where
    Nil : Assignable [] []

    (::) : forall t1, t2, ts1, ts2.
           (head : Assignable1 t1 t2) ->
           (tail : Assignable ts1 ts2) ->
           Assignable (t1 :: ts1) (t2 :: ts2)


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
  record Declaration where
    constructor Declare
    kind: Kind
    name: GoName
    type: GoType

  %runElab derive "GoName" [Generic, DecEq, DE.Eq]
  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Declaration" [Generic, DecEq]

  mutual
    ||| Set of declarations with unique names
    public export
    data Block : Type where
      Nil : Block
      (::) : (decl : Declaration) ->
             (rest : Block) ->
             (na : NameAbsent rest decl.name) =>
             Block

    public export
    data NameAbsent : (rest : Block) -> (name : GoName) -> Type where
      Wrap : forall rest, name.
             (so : So $ isNameAbsent rest name) ->
             NameAbsent rest name


    public export
    isNameAbsent : Block -> GoName -> Bool
    isNameAbsent [] _ = True
    isNameAbsent (Declare _ headName _ :: tail) newName =
      headName /= newName && isNameAbsent tail newName

  public export
  data ByType : Block -> GoType -> Declaration -> Type where
    Here : forall kind, name, ty, rest.
           (na : NameAbsent rest name) =>
           ByType (Declare kind name ty :: rest)
                  ty
                  (Declare kind name ty)

    There : forall decl, ty, head, rest.
            (there : ByType rest ty decl) ->
            (na : NameAbsent rest head.name) =>
            ByType (head :: rest) ty decl

  public export
  data DeclareIn : (block : Block) ->
                   (kind : Kind) ->
                   (ty : GoType) ->
                   (newName : GoName) ->
                   (newBlock : Block) ->
                   Type where
    MkDeclareIn : forall block, kind, ty, newName.
                  (na : NameAbsent block newName) =>
                  DeclareIn block kind ty newName
                            (Declare kind newName ty :: block)



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

  public export
  data DeclareIn : (ctxt : Context) ->
                   (kind : Kind) ->
                   (ty : GoType) ->
                   (newName : GoName) ->
                   (newCtxt : Context) ->
                   Type where
    MkDeclareIn : forall ctxt, kind, ty, newName, newBlock.
                  (di : DeclareIn ctxt.activeBlock kind ty newName newBlock) =>
                  DeclareIn ctxt kind ty newName
                            (MkContext newBlock ctxt.returns ctxt.shouldReturn)


namespace Expr
  public export
  data Literal : (ty : GoType) -> Type where
    MkInt : Nat -> Literal GoInt
    MkBool : Bool -> Literal GoBool

  -- @WHEN EXTRA_BUILTINS
  -- @ public export
  -- @ data PrefixOp : (argTy, resTy : GoType) -> Type where
    -- @ BoolNot : PrefixOp GoBool GoBool
    -- @ IntNeg : PrefixOp GoInt GoInt
  -- @END EXTRA_BUILTINS

  public export
  data InfixOp : (lhvTy, rhvTy, resTy : GoType) -> Type where
    IntAdd : InfixOp GoInt GoInt GoInt

    -- @WHEN EXTRA_BUILTINS
    -- @ IntSub, IntMul : InfixOp GoInt GoInt GoInt
    -- @ BoolAnd, BoolOr : InfixOp GoBool GoBool GoBool
    -- @ IntEq, IntNE, IntLt, IntLE, IntGt, IntGE : InfixOp GoInt GoInt GoBool
    -- @END EXTRA_BUILTINS

  public export
  data  BuiltinFunc : (paramTypes, retTypes : GoTypes) -> Type where
    -- @WHEN ASSIGNABLE_ANY
    -- @ Print : BuiltinFunc [GoAny] []
    -- @UNLESS ASSIGNABLE_ANY
    Print : BuiltinFunc [GoInt] []
    -- @END ASSIGNABLE_ANY

    -- @WHEN EXTRA_BUILTINS
    -- @ Max, Min : BuiltinFunc [GoInt, GoInt] [GoInt]
    -- @END EXTRA_BUILTINS

  mutual
    public export
    data ExprList : (ctxt : Context) -> (rets : GoTypes) -> Type where
      Nil : forall ctxt. ExprList ctxt []
      (::) : forall ctxt.
             (head : Expr ctxt [headTy]) ->
             (tail : ExprList ctxt tailTypes) ->
             ExprList ctxt (headTy :: tailTypes)

    public export
    data Expr : (ctxt : Context) -> (res : GoTypes) -> Type where
      GetLiteral : forall ctxt, resTy.
                   (lit : Literal resTy) ->
                   Expr ctxt [resTy]

      -- @WHEN EXTRA_BUILTINS
      -- @ ApplyPrefix : forall ctxt, resTy, argTy.
                    -- @ (op : PrefixOp argTy resTy) ->
                    -- @ (arg : Expr ctxt [argTy]) ->
                    -- @ Expr ctxt [resTy]
      -- @END EXTRA_BUILTINS

      ApplyInfix : forall ctxt, resTy, lhvTy, rhvTy.
                   (op : InfixOp lhvTy rhvTy resTy) ->
                   (lhv : Expr ctxt [lhvTy]) ->
                   (rhv : Expr ctxt [rhvTy]) ->
                   Expr ctxt [resTy]

      CallBuiltin : forall ctxt, paramTypes, argTypes, retTypes.
                    (f : BuiltinFunc paramTypes retTypes) ->
                    (a : Assignable paramTypes argTypes) =>
                    (args : Expr ctxt argTypes) ->
                    Expr ctxt retTypes

      -- CallNamed : forall ctxt, retTypes.
      --             (idx : Fin ctxt.depth) ->
      --             (isFunc : DefReturns ctxt.declarations idx retTypes) =>
      --             (params : Expr ctxt (ParamTypes ctxt.declarations idx {isFunc = isFunc})) ->
      --             Expr ctxt retTypes

      -- GetVar : forall ctxt, ty.
      --          (decl : Declaration) ->
      --          ByType ctxt.activeBlock ty decl =>
      --          Expr ctxt [ty]

      -- CallExpr : forall ctxt, argTypes, retTypes.
      --            (f : Expr ctxt [GoFunc argTypes retTypes]) ->
      --            (args : Expr ctxt argTypes) ->
      --            Expr ctxt retTypes

      MultiVal : forall ctxt.
                 {rets : GoTypes} ->
                 (vals : ExprList ctxt rets) ->
                 Expr ctxt rets


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

  public export
  data Statement : (ctxt : Context) -> Type where
    DeclareVar : forall ctxt.
                 (ty : GoType) ->
                 (initial : Expr ctxt [ty]) ->
                 (newName : GoName) ->
                 {newCtxt : Context} ->
                 (d : DeclareIn ctxt Var ty newName newCtxt) =>
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

    -- @WHEN IF_STMTS
    -- @ InnerIf : forall ctxt.
              -- @ (test : Expr ctxt [GoBool]) ->
              -- @ {ctxtThen, ctxtElse : Context} ->
              -- @ AllowInnerIf ctxt ctxtThen ctxtElse =>
              -- @ (th : Statement ctxtThen) ->
              -- @ (el : Statement ctxtElse) ->
              -- @ (cont : Statement ctxt) ->
              -- @ Statement ctxt

    -- @ TermIf : forall ctxt.
             -- @ ShouldReturn ctxt =>
             -- @ (test : Expr ctxt [GoBool]) ->
             -- @ (th : Statement ctxt) ->
             -- @ (el : Statement ctxt) ->
             -- @ Statement ctxt
    -- @END IF_STMTS

  export
  isEmpty : forall ctxt. Statement ctxt -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs : Fuel -> (ctxt : Context) -> (rets : GoTypes) ->
                   Gen MaybeEmpty $ Expr ctxt rets
