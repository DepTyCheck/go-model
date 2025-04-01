module Language.Go.Model

import Data.Fuel
import Data.Nat
import Data.Fin
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE

import Generics.Derive

import Test.DepTyCheck.Gen

%language ElabReflection
%unbound_implicits off

namespace GoType
  mutual
    ||| Types from Go Language
    |||
    ||| GoInt <-> int
    ||| GoAny <-> interface {}
    ||| Note: GoAny can slow down generation if there are any non constructible types
    public export
    data GoType
      = GoInt
      | GoBool
      | GoFunc GoTypes GoTypes
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

  mutual
    %runElab derive "GoType" [Generic, DecEq]

    export
    DecEq GoTypes where
      decEq Nil Nil = Yes Refl
      decEq Nil (_ :: _) = No $ \case Refl impossible
      decEq (_ :: _) Nil = No $ \case Refl impossible
      decEq (xs :: x) (xs' :: x') = assert_total decEqCong2 (decEq xs xs') (decEq x x')

  public export
  data GoTypeEq : GoType -> GoType -> Type where
    Refl : forall ty. GoTypeEq ty ty


namespace Assignable
  -- @WHEN ASSIGNABLE_ANY
  -- @ public export
  -- @ data Assignable1 : (lhv, rhv : GoType) -> Type where
    -- @ AssignSame : forall t. Assignable1 t t

    -- @ AssignToAny :  forall t. Assignable1 GoAny t

  -- @ public export
  -- @ data Assignable : (lhv, rhv : GoTypes) -> Type where
    -- @ Nil : Assignable [] []

    -- @ (::) : forall t1, t2, ts1, ts2.
           -- @ (head : Assignable1 t1 t2) ->
           -- @ (tail : Assignable ts1 ts2) ->
           -- @ Assignable (t1 :: ts1) (t2 :: ts2)
  -- @UNLESS ASSIGNABLE_ANY
  public export
  data Assignable : (lhv, rhv : GoTypes) -> Type where
    Refl : forall ts. Assignable ts ts
  -- @END ASSIGNABLE_ANY


namespace Declaration
  public export
  data Kind
    = Var
    | Const
    | Func

  public export
  record Declaration where
    constructor Declare
    kind: Kind
    type: GoType

  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Declaration" [Generic, DecEq]


  public export
  data Stack : (depth : Nat) -> Type where
    Nil : Stack 0
    (::) : forall len. Declaration -> Stack len -> Stack (S len)


  public export
  append : forall len. Declaration -> Stack len -> Stack (S len)
  append decl Nil = [decl]
  append decl (d :: ds) = d :: append decl ds


  public export
  index : forall len. Fin len -> Stack len -> Declaration
  index FZ (d :: _) = d
  index (FS i) (_ :: ds) = index i ds

  public export
  data ByType : forall len. GoType -> Stack len ->
                            Fin len -> Declaration -> Type where
    HereT : forall ty, head, tail.
            GoTypeEq ty head.type =>
            ByType ty (head :: tail) FZ head

    ThereT : forall ty, head, tail, idx, found.
             ByType ty tail idx found ->
             GoTypeEq ty found.type =>  -- TODO: is it slow?
             ByType ty (head :: tail) (FS idx) found

    -- public export
    -- data NameAbsent : (rest : Block) -> (name : GoName) -> Type where
    --   Wrap : forall rest, name.
    --          (oh : So $ isNameAbsent rest name) ->
    --          NameAbsent rest name


    -- public export
    -- isNameAbsent : Block -> GoName -> Bool
    -- isNameAbsent [] _ = True
    -- isNameAbsent (Declare _ headName _ :: tail) newName =
    --   headName /= newName && isNameAbsent tail newName


  -- public export
  -- data ByRetB : Block -> Kind -> GoName -> (args, rets : GoTypes) -> Type where
  --   HereB' : forall kind, name, args, rets, rest.
  --            (na : NameAbsent rest name) =>
  --            ByRetB (Declare kind name (GoFunc args rets) :: rest)
  --                  kind name args rets

  --   ThereB' : forall kind, name, args, rets, rest, hKind, hName, hTy.
  --             (there : ByRetB rest kind name args rets) ->
  --             (na : NameAbsent rest hName) =>
  --             ByRetB (Declare hKind hName hTy :: rest) kind name args rets

  -- public export
  -- data BlockOf : GoTypes -> Block -> Type where

  --   BlockOfNil : BlockOf [] []

  --   BlockOfCons : forall t, ts, tail.
  --                 (tailCond : BlockOf ts tail) =>
  --                 (newName : GoName) ->
  --                 (na : NameAbsent tail newName) =>
  --                 BlockOf (t :: ts) (Declare Var newName t :: tail)


namespace Context
  public export
  record Context where
    constructor MkContext
    stackDepth : Nat
    stack : Stack stackDepth
    returns : GoTypes
    isTerminating : Bool

  public export
  SetReturns : GoTypes -> Context -> Context
  SetReturns rets = { isTerminating := True, returns := rets }

  public export
  SetIsTerminating : Bool -> Context -> Context
  SetIsTerminating value = { isTerminating := value }


namespace Statement
  public export
  data Statement : (ctxt : Context) -> Type


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
      (::) : forall ctxt, headTy, tailTypes.
             (head : Expr ctxt [headTy]) ->
             (tail : ExprList ctxt tailTypes) ->
             ExprList ctxt (headTy :: tailTypes)

    public export
    data Expr : (ctxt : Context) -> (res : GoTypes) -> Type where
      -- AnonFunc : forall ctxt, paramTypes.
      --            {retTypes : GoTypes} ->
      --            (paramBlock : Block) ->
      --            (pb : BlockOf paramTypes paramBlock) =>
      --            (body : Statement (SetReturns retTypes $
      --                               PutBlock paramBlock ctxt)) ->
      --            Expr ctxt [GoFunc paramTypes retTypes]

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
      --             (kind : Kind) ->
      --             (name : GoName) ->
      --             (argTypes : GoTypes) ->
      --             (br : ByRetS ctxt.blocks kind name argTypes retTypes) =>
      --             (args : ExprList ctxt argTypes) ->
      --             Expr ctxt retTypes

      GetDecl : forall ctxt, ty.
                (idx : Fin (ctxt.stackDepth)) ->
                (decl : Declaration) ->
                (bt : ByType ty ctxt.stack idx decl) =>
                Expr ctxt [ty]

      -- CallExpr : forall ctxt, argTypes, retTypes.
      --            (f : Expr ctxt [GoFunc argTypes retTypes]) ->
      --            (args : Expr ctxt argTypes) ->
      --            Expr ctxt retTypes

      -- Comma : forall ctxt.
      --         {aTy, bTy : GoType} ->
      --         {restTypes : GoTypes} ->
      --         (a : Expr ctxt [aTy]) ->
      --         (b : Expr ctxt [bTy]) ->
      --         (rest : ExprList ctxt restTypes) ->
      --         Expr ctxt (aTy :: bTy :: restTypes)


namespace Statement
  public export
  data AllowJustStop : Context -> Type where
    StopUnlessShouldReturn : AllowJustStop (MkContext { isTerminating = False, _ })
    StopWhenReturnNone : AllowJustStop (MkContext { returns = [], _ })

  public export
  data AllowReturnValue : Context -> Type where
    MkAllowRetrunValue : forall ret, rets, stackDepth.
                         {0 stack : Stack stackDepth} ->
                         AllowReturnValue (MkContext
                                          { isTerminating = True
                                          , returns = ret :: rets
                                          , stack = stack
                                          , stackDepth = stackDepth
                                          })

  public export
  data AllowReturnNone : Context -> Type where
    MkAllowRetrunNone : AllowReturnNone (MkContext
                                        { isTerminating = True
                                        , returns = []
                                        , _
                                        })

  -- @WHEN IF_STMTS
  -- @ public export
  -- @ data AllowInnerIf : (isTermThen : Bool) ->
                      -- @ (isTermElse : Bool) ->
                      -- @ Type where
    -- @ AllowInnerIfTT : AllowInnerIf True True
    -- @ AllowInnerIfTF : AllowInnerIf True False
    -- @ AllowInnerIfFT : AllowInnerIf False True
  -- @END IF_STMTS

  public export
  OnDeclare : Kind -> GoType -> Context -> Context
  OnDeclare kind type =
    { stackDepth $= S
    , stack $= append (Declare kind type)
    }

  public export
  record DeclareStmt (ctxt : Context) Kind where
    constructor MkDeclareStmt
    type : GoType
    initial : Expr ctxt [type]
    cont : Statement (OnDeclare Var type ctxt)

  data Statement : (ctxt : Context) -> Type where
    DeclareVar : forall ctxt.
                 (decl : DeclareStmt ctxt Var) ->
                 Statement ctxt

    JustStop : forall ctxt.
               (a : AllowJustStop ctxt) =>
               Statement ctxt

    ReturnValue : forall ctxt.
                  (a : AllowReturnValue ctxt) =>
                  (res : Expr ctxt ctxt.returns) ->
                  Statement ctxt

    ReturnNone : forall ctxt.
                 (a : AllowReturnNone ctxt) =>
                 Statement ctxt

    VoidExpr : forall ctxt.
               (expr : Expr ctxt []) ->
               (cont : Statement ctxt) ->
               Statement ctxt

    -- @WHEN IF_STMTS
    -- @ InnerIf : forall ctxt.
              -- @ (test : Expr ctxt [GoBool]) ->
              -- @ {isTermThen, isTermElse: Bool} ->
              -- @ (ai : AllowInnerIf isTermThen isTermElse) =>
              -- @ (th : Statement $ SetIsTerminating isTermThen ctxt) ->
              -- @ (el : Statement $ SetIsTerminating isTermElse ctxt) ->
              -- @ (cont : Statement ctxt) ->
              -- @ Statement ctxt

    -- @ TermIf : forall ctxt, ret.
             -- @ IsTerminating ctxt ret =>
             -- @ (test : Expr ctxt [GoBool]) ->
             -- @ (th : Statement ctxt) ->
             -- @ (el : Statement ctxt) ->
             -- @ Statement ctxt
    -- @END IF_STMTS

export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs : Fuel -> (ctxt : Context) -> (rets : GoTypes) ->
                   Gen MaybeEmpty $ Expr ctxt rets
