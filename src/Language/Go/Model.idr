module Language.Go.Model

import Data.Fin
import Data.Fin.Properties
import Data.Fuel
import Data.Nat
import Data.Nat.Order.Properties

import Decidable.Equality

import Generics.Derive

import Test.DepTyCheck.Gen

import Syntax.PreorderReasoning

%language ElabReflection
%default total
%unbound_implicits off

%hide Language.Reflection.TTImp.Decl


public export
data BoolEqual : Bool -> Bool -> Type where
  Refl : forall b. BoolEqual b b


public export
data IsZero : Nat -> Type where
  ItIsZero : IsZero Z


public export
data GoType : Type

namespace TypeVect
  public export
  data TypeVect : (len : Nat) -> Type where
    Nil  : TypeVect 0
    (::) : forall len. GoType -> TypeVect len -> TypeVect (S len)

public export
record GoFuncType where
  constructor To
  {parLen, retLen : Nat}
  par : TypeVect parLen
  ret : TypeVect retLen

data GoType : Type where
  GoInt  : GoType
  GoBool : GoType
  GoFunc : GoFuncType -> GoType
  -- @WHEN ASSIGNABLE_ANY
-- @   | GoAny
  -- @END ASSIGNABLE_ANY


export
Biinjective TypeVect.(::) where
  biinjective Refl = (Refl, Refl)

export
Injective GoFunc where
  injective Refl = Refl


mutual
  %runElab derive "GoType" [Generic, DecEq]

  export
  {0 len : Nat} -> DecEq (TypeVect len) where
    decEq Nil Nil = Yes Refl
    decEq (t1 :: ts1) (t2 :: ts2) =
      assert_total decEqCong2 (decEq t1 t2) (decEq ts1 ts2)

  export
  DecEq GoFuncType where
    decEq
        (To {parLen} {retLen} par ret)
        (To {parLen = parLen'} {retLen = retLen'} par' ret')
      =
        let Yes Refl  := decEq parLen parLen'
              | No contra => No $ \eq => contra $ fst $ injDP eq
            Yes Refl  := decEq retLen retLen'
              | No contra => No $ \eq => contra $ fst $ snd $ injDP eq
            Yes parEq := decEq par par'
              | No contra => No $ \eq => contra $ fst $ snd $ snd $ injDP eq
            Yes retEq := decEq ret ret'
              | No contra => No $ \eq => contra $ snd $ snd $ snd $ injDP eq
         in Yes $ congDP parEq retEq

      where
        congDP:
             forall par, par', ret, ret'
          .  (0 _              : (par = par'))
          -> (0 _              : (ret = ret'))
          -> (To par ret = To par' ret')
        congDP Refl Refl = Refl

        injDP:
             forall parLen, parLen', retLen, retLen'
          .  {0 par  : TypeVect parLen}
          -> {0 par' : TypeVect parLen'}
          -> {0 ret  : TypeVect retLen}
          -> {0 ret' : TypeVect retLen'}
          -> (0 _    : (To par ret = To par' ret'))
          -> (parLen = parLen', retLen = retLen', par = par', ret = ret')
        injDP Refl = (Refl, Refl, Refl, Refl)


-- data IsEmpty : forall len. TypeVect len -> Type where
--   [search len]
--   ItIsEmpty : IsEmpty []


-- data NonEmpty : forall len. TypeVect len -> Type where
--   [search len]
--   IsNonEmpty : forall head, tail. NonEmpty (head :: tail)


-- @WHEN ASSIGNABLE_ANY
-- @ public export
-- @ data Assignable1 : (lhv, rhv : GoType) -> Type where
-- @   AssignSame : forall t. Assignable1 t t

-- @   AssignToAny :  forall t. Assignable1 GoAny t

-- @ public export
-- @ data Assignable : (lhv, rhv : GoTypes) -> Type where
-- @   Nil : Assignable [] []

-- @   (::) : forall t1, t2, ts1, ts2.
-- @          (head : Assignable1 t1 t2) ->
-- @          (tail : Assignable ts1 ts2) ->
-- @          Assignable (t1 :: ts1) (t2 :: ts2)
-- @END ASSIGNABLE_ANY


public export
data Kind
  = Var
  | Const
  | Func

public export
record Decl where
  constructor MkDecl
  kind : Kind
  type : GoType


namespace Stack
  public export
  data Stack : (len : Nat) -> Type where
    Lin  : Stack Z
    (:<) : forall len. Stack len -> Decl -> Stack (S len)


push:
     forall len, count
  .  Kind
  -> TypeVect count
  -> Stack len
  -> Stack (len + count)
push _ [] stack = rewrite plusZeroRightNeutral len in stack
push {len} {count = S count'} kind (t :: ts) stack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind ts $ stack :< MkDecl kind t


public export
data ByType : forall len. GoType -> Stack len -> Fin len -> Type where
  HereT:
       forall ty, kind, tail
    .  ByType ty (tail :< MkDecl kind ty) FZ

  ThereT:
       forall ty, head, tail, found
    .  (there : ByType ty tail found)
    -> ByType ty (tail :< head) (FS found)


public export
data ByRet:
     forall len, parLen, retLen
  .  (par : TypeVect parLen)
  -> (ret : TypeVect retLen)
  -> Stack len
  -> Fin len
  -> Type
  where

  HereR:
       forall par, ret, kind, tail
    .  ByRet par ret (tail :< MkDecl kind (GoFunc $ par `To` ret)) FZ

  ThereR:
       forall par, ret, head, tail, found
    .  (there : ByRet par ret tail found)
    -> ByRet par ret (tail :< head) (FS found)


public export
record Context where
  constructor MkContext
  stackLen      : Nat
  stack         : Stack stackLen
  blockDepth    : Fin (S stackLen)
  returnsLen    : Nat
  returns       : TypeVect returnsLen
  isTerminating : Bool

public export
SetIsTerminating : Bool -> Context -> Context
SetIsTerminating value = { isTerminating := value }


public export
data Statement : (ctxt : Context) -> Type


public export
data Literal : (ty : GoType) -> Type where
  MkInt  : Nat  -> Literal GoInt
  MkBool : Bool -> Literal GoBool

-- @WHEN EXTRA_BUILTINS
public export
data PrefixOp : (argTy, resTy : GoType) -> Type where
  BoolNot : PrefixOp GoBool GoBool
  IntNeg  : PrefixOp GoInt GoInt
-- @END EXTRA_BUILTINS

public export
data InfixOp : (lhvTy, rhvTy, resTy : GoType) -> Type where
  IntAdd : InfixOp GoInt GoInt GoInt

  -- @WHEN EXTRA_BUILTINS
  IntSub, IntMul  : InfixOp GoInt GoInt GoInt
  BoolAnd, BoolOr : InfixOp GoBool GoBool GoBool
  IntEq, IntNE, IntLt, IntLE, IntGt, IntGE : InfixOp GoInt GoInt GoBool
  -- @END EXTRA_BUILTINS

public export
data  BuiltinFunc:
     forall parLen, retLen
  .  (parTypes : TypeVect parLen)
  -> (retTypes : TypeVect retLen)
  -> Type
  where

-- @WHEN ASSIGNABLE_ANY
-- @     Print : BuiltinFunc [GoAny] []
-- @UNLESS ASSIGNABLE_ANY
    Print : BuiltinFunc [GoInt] []
-- @END ASSIGNABLE_ANY

-- @WHEN EXTRA_BUILTINS
    Max, Min : BuiltinFunc [GoInt, GoInt] [GoInt]
-- @END EXTRA_BUILTINS


public export
data Expr : forall len. (ctxt : Context) -> (res : TypeVect len) -> Type


namespace ExprList
  public export
  data ExprList:
       (ctxt  : Context)
    -> {len   : Nat}
    -> (types : TypeVect len)
    -> Type
    where
      Nil : forall ctxt. ExprList ctxt []

      (::):
           forall ctxt, headT, tailLen
        .  {0 tailT : TypeVect tailLen}
        -> (head    : Expr ctxt [headT])
        -> (tail    : ExprList ctxt tailT)
        -> ExprList ctxt (headT :: tailT)


public export
data MaybeNoValue:
     (ctxt  : Context)
  -> {len   : Nat}
  -> (types : TypeVect len)
  -> Type
  where

    NoValue: forall ctxt. MaybeNoValue ctxt []

    Value:
         forall ctxt, t, ts
      .  (expr : Expr ctxt (t :: ts))
      -> MaybeNoValue ctxt (t :: ts)


public export
OnAnonFunc:
     {parLen, retLen : Nat}
  -> (ctxt     : Context)
  -> (parTypes : TypeVect parLen)
  -> (retTypes : TypeVect retLen)
  -> Context
OnAnonFunc {parLen} ctxt newTypes retTypes =
  { stackLen      $= (+ parLen)
  , stack         $= push Var newTypes
  , blockDepth    := natToFinLT @{prf parLen ctxt.stackLen} parLen
  , returnsLen    := retLen
  , returns       := retTypes
  , isTerminating := True
  } ctxt

  where
    0 prf : (0 a, b : Nat) -> LT a (S $ b + a)
    prf a b = rewrite plusCommutative b a in
                LTESucc $ lteAddRight {m = b} a


data Expr : forall len. (ctxt : Context) -> (res : TypeVect len) -> Type where
-- @WHEN HOLES
-- @   Hole:
-- @        forall ctxt, res
-- @     .  Expr ctxt res
-- @END HOLES

  Comma:
       forall ctxt, aT, bT, restT
    .  (a          : Expr ctxt [aT])
    -> (b          : Expr ctxt [bT])
    -> (rest       : ExprList ctxt restT)
    -> Expr ctxt (aT :: bT :: restT)

  AnonFunc:
       forall ctxt, retTypes
    .  {parCount   : Nat}
    -> {0 parTypes : TypeVect parCount}
    -> (body       : Statement (OnAnonFunc ctxt parTypes retTypes))
    -> Expr ctxt [GoFunc $ parTypes `To` retTypes]

  GetLiteral:
       forall ctxt, resTy
    .  (lit        : Literal resTy)
    -> Expr ctxt [resTy]

  -- @WHEN EXTRA_BUILTINS
  ApplyPrefix:
       forall ctxt
    .  {argT, resT : GoType}
    -> (op         : PrefixOp argT resT)
    -> (arg : Expr ctxt [argT])
    -> Expr ctxt [resT]
  -- @END EXTRA_BUILTINS

  ApplyInfix:
       forall ctxt, resT
    .  {lhvT, rhvT : GoType}
    -> (op         : InfixOp lhvT rhvT resT)
    -> (lhv        : Expr ctxt [lhvT])
    -> (rhv        : Expr ctxt [rhvT])
    -> Expr ctxt [resT]

  CallBuiltin:
       forall ctxt, retTypes
    .  {parLen     : Nat}
    -> {parTypes   : TypeVect parLen}
    -> (func       : BuiltinFunc parTypes retTypes)
    -> (args       : ExprList ctxt parTypes)
    -> Expr ctxt retTypes

  CallNamed:
       forall ctxt, retT
    .  {parLen     : Nat}
    -> (idx        : Fin ctxt.stackLen)
    -> {parT       : TypeVect parLen}
    -> (args       : MaybeNoValue ctxt parT)
    -> {auto 0 br  : ByRet parT retT ctxt.stack idx}
    -> Expr ctxt retT

  GetDecl:
       forall ctxt, ty
    .  (idx        : Fin ctxt.stackLen)
    -> {auto 0 bt  : ByType ty ctxt.stack idx}
    -> Expr ctxt [ty]

  -- CallExpr : forall ctxt, argTypes, retTypes.
  --            (f : Expr ctxt [GoFunc argTypes retTypes]) ->
  --            (args : Expr ctxt argTypes) ->
  --            Expr ctxt retTypes


public export
data MaybeCont : (isTerm : Bool) -> (newCtxt : Context) -> Type where
  Just    : forall ctxt. (cont : Statement ctxt) -> MaybeCont False ctxt
  Nothing : forall ctxt. MaybeCont True ctxt


-- @WHEN IF_STMTS
public export
data IfTerm : (isIfTerm, isThenTerm, isElseTerm : Bool) -> Type where
  TTT : IfTerm True True True
  FAA : forall th, el. IfTerm False th el


-- @END IF_STMTS


public export
OnDeclare:
     {count    : Nat}
  -> (ctxt     : Context)
  -> (kind     : Kind)
  -> (newTypes : TypeVect count)
  -> Context
OnDeclare ctxt kind newTypes =
  { stackLen   $= (+ count)
  , stack      $= push kind newTypes
  , blockDepth := rewrite plusCommutative ctxt.stackLen count in
                    rewrite plusSuccRightSucc count ctxt.stackLen in
                      shift count ctxt.blockDepth
  } ctxt


data Statement : (ctxt : Context) -> Type where
  JustStop:
       {0 ctxt      : Context}
    -> {auto 0 nt   : BoolEqual ctxt.isTerminating False}
    -> Statement ctxt

  Return:
       {0 ctxt      : Context}
    -> {auto 0 term : BoolEqual ctxt.isTerminating True}
    -> (res         : MaybeNoValue ctxt ctxt.returns)
    -> Statement ctxt

  Var':
       {0 ctxt      : Context}
    -> {count       : Nat}
    -> (newTypes    : TypeVect count)
    -> (initial     : Expr ctxt newTypes)
    -> (cont        : Statement (OnDeclare ctxt Var newTypes))
    -> Statement ctxt

  -- @WHEN IF_STMTS
  If:
       forall ctxt
    .  {tt, et      : Bool}
    -> {auto 0 term : IfTerm ctxt.isTerminating tt et}
    -> (test        : Expr ctxt [GoBool])
    -> (then_       : Statement $ SetIsTerminating tt ctxt)
    -> (else_       : Statement $ SetIsTerminating et ctxt)
    -> (cont : MaybeCont ctxt.isTerminating ctxt)
    -> Statement ctxt
  -- @END IF_STMTS


export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs:
     Fuel
  -> {retLen : Nat}
  -> (ctxt   : Context)
  -> (ret    : TypeVect retLen)
  -> Gen MaybeEmpty $ Expr ctxt ret

