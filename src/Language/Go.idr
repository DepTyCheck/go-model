module Language.Go

import Data.Fuel
import Data.Nat
import Data.Fin
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE

import Generics.Derive

import Utils.MkVect

import Test.DepTyCheck.Gen

%language ElabReflection
%unbound_implicits off

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

namespace Assignable
  public export
  data Assignable1 : (lhv, rhv : GoType) -> Type where
    AssignSame : forall t. Assignable1 t t
    -- AssignToAny :  forall t. Assignable1 GoAny t

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


namespace Builtins
  public export
  record PrefixOp where
    constructor MkPrefixOp
    name : String
    argumentType : GoType
    returnType : GoType

  %runElab mkListType "PrefixOp" "PrefixOpList"
  %runElab derive "PrefixOp" [Generic, DecEq]

  namespace PrefixOp
    public export
    data ByType : PrefixOpList -> GoType -> PrefixOp -> Type where
      Here : forall n, a, ret, rest.
             ByType (MkPrefixOp n a ret :: rest) ret
                    (MkPrefixOp n a ret)

      There : forall x, rest, ty, op.
              (next : ByType rest ty op) ->
              ByType (x :: rest) ty op

  public export
  record InfixOp where
    constructor MkInfixOp
    name : String
    lhvType : GoType
    rhvType : GoType
    returnType : GoType

  %runElab mkListType "InfixOp" "InfixOpList"
  %runElab derive "InfixOp" [Generic, DecEq]

  namespace InfixOp
    public export
    data ByType : InfixOpList -> GoType -> InfixOp -> Type where
      Here : forall n, lt, rt, ret, rest.
             ByType (MkInfixOp n lt rt ret :: rest) ret
                    (MkInfixOp n lt rt ret)

      There : forall x, rest, ty, op.
              (next : ByType rest ty op) ->
              ByType (x :: rest) ty op


  public export
  record BuiltinFunc where
    constructor MkBuiltinFunc
    name : String
    paramTypes : GoTypes
    returnTypes : GoTypes

  %runElab mkListType "BuiltinFunc" "BuiltinFuncList"
  %runElab derive "BuiltinFunc" [Generic, DecEq]

  namespace BuiltinFunc
    public export
    data ByType : BuiltinFuncList -> GoTypes -> BuiltinFunc -> Type where
      Here : forall n, args, ret, rest.
             ByType (MkBuiltinFunc n args ret :: rest) ret
                    (MkBuiltinFunc n args ret)

      There : forall x, rest, ty, op.
              (next : ByType rest ty op) ->
              ByType (x :: rest) ty op

  public export
  record Builtins where
    constructor MkBuiltins
    prefixOps : PrefixOpList
    infixOps : InfixOpList
    builtinFuncs : BuiltinFuncList

namespace Context
  public export
  record Context where
    constructor MkContext
    builtins : Builtins
    activeBlock : Block
    returns : GoTypes
    shouldReturn : Bool

  -- public export
  -- data AddDeclaration : (ctxt : Context) ->
  --                       (decl : Declaration) ->
  --                       (newCtxt : Context) ->
  --                      Type where
  --   AddUnchecked : AddDeclaration ctxt decl (MkContext
  --                       (decl :: ctxt.activeBlock)
  --                       ctxt.returns
  --                       ctxt.shouldReturn)

  -- public export
  -- data AddDeclaration : (ctxt : Context) ->
  --                       (decl : Declaration) ->
  --                       (newCtxt : Context) ->
  --                       Type where
  --   AddUnchecked : AddDeclaration
  --                   (MkContext oldBlock rets sr)
  --                   decl
  --                   (MkContext (decl :: oldBlock) rets sr)

  public export
  AddDeclaration1 : Context -> Declaration -> Context
  AddDeclaration1 ctxt decl = { activeBlock $= (::) decl } ctxt


namespace Expr
  public export
  data Literal : (ty : GoType) -> Type where
    MkInt : Nat -> Literal GoInt
    MkBool : Bool -> Literal GoBool

  mutual
    public export
    data ExprList : (ctxt : Context) -> (rets : GoTypes) -> Type where
      Nil : forall ctxt. ExprList ctxt []
      (::) : forall ctxt, headTy, tailTypes.
             (head : Expr ctxt [headTy]) ->
             (tail : ExprList ctxt tailTypes) ->
             ExprList ctxt (headTy :: tailTypes)

    public export
    data Expr : (ctxt : Context) -> (res : GoTypes) -> Type where
      GetLiteral : forall ctxt, resTy.
                   (lit : Literal resTy) ->
                   Expr ctxt [resTy]

      ApplyPrefix : forall ctxt, resTy.
                    (op : PrefixOp) ->
                    (findOp : ByType ctxt.builtins.prefixOps resTy op) =>
                    (arg : Expr ctxt [op.argumentType]) ->
                    Expr ctxt [resTy]

      ApplyInfix : forall ctxt, resTy.
                   (op : InfixOp) ->
                   (findOp : ByType ctxt.builtins.infixOps resTy op) =>
                   (lhv : Expr ctxt [op.lhvType]) ->
                   (rhv : Expr ctxt [op.rhvType]) ->
                   Expr ctxt [resTy]

      CallBuiltin : forall ctxt, argTypes, retTypes.
                    (f : BuiltinFunc) ->
                    (findOp : ByType ctxt.builtins.builtinFuncs retTypes f) =>
                    (a : Assignable f.paramTypes argTypes) =>
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
    AllowReturnWhenShould : forall a, b, types.
                            AllowReturn (MkContext a b types True) types

  public export
  data AllowInnerIf : (ctxt, ctxtThen, ctxtElse : Context) ->
                      Type where
    MkAllowInnerIf : forall b, d, r, t1, t2.
                     AllowInnerIf (MkContext b d r False)
                                  (MkContext b d r t1)
                                  (MkContext b d r t2)

  public export
  data ShouldReturn : Context -> Type where
    MkShouldReturn : ShouldReturn (MkContext _ _ _ True)

  public export
  data Statement : (ctxt : Context) -> Type where
    DeclareVar : forall ctxt.
                 (name : GoName) ->
                 (new : So $ isNewName ctxt.activeBlock name) =>
                 (ty : GoType) ->
                 (initial : Expr ctxt [ty]) ->
                 {newCtxt : Context} ->
                 -- (AddDeclaration ctxt (Declare Var name ty) newCtxt) =>
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

  export
  isEmpty : forall ctxt. Statement ctxt -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs : Fuel -> (ctxt : Context) -> (rets : GoTypes) ->
                   Gen MaybeEmpty $ Expr ctxt rets
