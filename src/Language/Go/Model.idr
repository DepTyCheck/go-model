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
  -- GoChan : GoType -> GoType
  -- @WHEN ASSIGNABLE_ANY
-- @   | GoAny
  -- @END ASSIGNABLE_ANY

namespace MaybeType
  public export
  data MaybeType
    = Just GoType
    | Nothing


export
Biinjective TypeVect.(::) where
  biinjective Refl = (Refl, Refl)

export
Injective GoFunc where
  injective Refl = Refl

-- export
-- Injective GoChan where
--   injective Refl = Refl


export
{0 len : Nat} -> DecEq (TypeVect len)

export
DecEq GoFuncType

export
DecEq GoType where
  decEq GoInt      GoInt       = Yes Refl
  decEq GoBool     GoBool      = Yes Refl
  decEq (GoFunc f) (GoFunc f') = decEqCong (decEq f f')
  -- decEq (GoChan t) (GoChan t') = decEqCong (decEq t t')
  decEq GoInt      GoBool      = No $ \case Refl impossible
  decEq GoInt      (GoFunc _)  = No $ \case Refl impossible
  -- decEq GoInt      (GoChan _)  = No $ \case Refl impossible
  decEq GoBool     GoInt       = No $ \case Refl impossible
  decEq GoBool     (GoFunc _)  = No $ \case Refl impossible
  -- decEq GoBool     (GoChan _)  = No $ \case Refl impossible
  decEq (GoFunc _) GoInt       = No $ \case Refl impossible
  decEq (GoFunc _) GoBool      = No $ \case Refl impossible
  -- decEq (GoFunc _) (GoChan _)  = No $ \case Refl impossible
  -- decEq (GoChan _) GoInt       = No $ \case Refl impossible
  -- decEq (GoChan _) GoBool      = No $ \case Refl impossible
  -- decEq (GoChan _) (GoFunc _)  = No $ \case Refl impossible

-- %runElab derive "GoType" [Generic, DecEq]

{0 len : Nat} -> DecEq (TypeVect len) where
  decEq Nil Nil = Yes Refl
  decEq (t1 :: ts1) (t2 :: ts2) =
    assert_total decEqCong2 (decEq t1 t2) (decEq ts1 ts2)

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
      congDP : forall par, par', ret, ret'.
               (0 _ : (par = par')) ->
               (0 _ : (ret = ret')) ->
               (To par ret = To par' ret')
      congDP Refl Refl = Refl

      injDP : forall parLen, parLen', retLen, retLen'.
              {0 par  : TypeVect parLen} ->
              {0 par' : TypeVect parLen'} ->
              {0 ret  : TypeVect retLen} ->
              {0 ret' : TypeVect retLen'} ->
              (0 _    : (To par ret = To par' ret')) ->
              (parLen = parLen', retLen = retLen', par = par', ret = ret')
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


push : forall len, count.
       Kind ->
       TypeVect count ->
       Stack len ->
       Stack (len + count)
push _ [] stack = rewrite plusZeroRightNeutral len in stack
push {len} {count = S count'} kind (t :: ts) stack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind ts $ stack :< MkDecl kind t


public export
data ByType : forall len. GoType -> Stack len -> Fin len -> Type where
  HereT  : forall ty, kind, tail.
           ByType ty (tail :< MkDecl kind ty) FZ

  ThereT : forall ty, head, tail, found.
           (there : ByType ty tail found) ->
           ByType ty (tail :< head) (FS found)

public export
data ByRet : forall len, parLen, retLen.
             (par : TypeVect parLen) ->
             (ret : TypeVect retLen) ->
             Stack len ->
             Fin len ->
             Type
  where

  HereR  : forall par, ret, kind, tail.
           ByRet par ret (tail :< MkDecl kind (GoFunc $ par `To` ret)) FZ

  ThereR : forall par, ret, head, tail, found.
           (there : ByRet par ret tail found) ->
           ByRet par ret (tail :< head) (FS found)


public export
byRetToByType : forall par, ret, stack, idx.
                ByRet par ret stack idx ->
                ByType (GoFunc $ par `To` ret) stack idx
byRetToByType HereR = HereT
byRetToByType (ThereR there) = ThereT (byRetToByType there)


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
setIsTerminating : Bool -> Context -> Context
setIsTerminating value = { isTerminating := value }


public export
data Statement : (ctxt : Context) -> Type


public export
data Literal : (ty : GoType) -> Type where
  MkInt  : Nat  -> Literal GoInt
  MkBool : Bool -> Literal GoBool

-- @WHEN EXTRA_BUILTINS
-- @ public export
-- @ data PrefixOp : (argTy, resTy : GoType) -> Type where
-- @   BoolNot  : PrefixOp GoBool GoBool
-- @   IntNeg   : PrefixOp GoInt GoInt
-- @   ChanRecv : forall t. PrefixOp (GoChan t) t
-- @END EXTRA_BUILTINS

public export
data InfixOp : (lhvTy, rhvTy, resTy : GoType) -> Type where
  IntAdd : InfixOp GoInt GoInt GoInt

  -- @WHEN EXTRA_BUILTINS
-- @   IntSub, IntMul  : InfixOp GoInt GoInt GoInt
-- @   BoolAnd, BoolOr : InfixOp GoBool GoBool GoBool
-- @   IntEq, IntNE, IntLt, IntLE, IntGt, IntGE : InfixOp GoInt GoInt GoBool
  -- @END EXTRA_BUILTINS

public export
data BuiltinFunc : forall parLen, retLen.
                   (type     : MaybeType) ->
                   (parTypes : TypeVect parLen) ->
                   (retTypes : TypeVect retLen) ->
                   Type
  where

  -- MakeChanUnbuf : forall t. BuiltinFunc (Just (GoChan t)) [] [GoChan t]
  -- MakeChanBuf   : forall t. BuiltinFunc (Just (GoChan t)) [GoInt] [GoChan t]

-- @WHEN ASSIGNABLE_ANY
-- @     Print : BuiltinFunc [GoAny] []
-- @UNLESS ASSIGNABLE_ANY
  Print : BuiltinFunc Nothing [GoInt] []
-- @END ASSIGNABLE_ANY

-- @WHEN EXTRA_BUILTINS
-- @   Max, Min : BuiltinFunc Nothing [GoInt, GoInt] [GoInt]
-- @END EXTRA_BUILTINS


namespace Expr
  public export
  data Expr : (ctxt : Context) -> (res : GoType) -> Type

-- namespace MultivaluedExpr
--   public export
--   data MultivaluedExpr : forall len.
--                          (ctxt  : Context) ->
--                          (types : TypeVect len) ->
--                          Type

namespace ExprList
  public export
  data ExprList : forall len.
                  (ctxt  : Context) ->
                  (types : TypeVect len) ->
                  Type where

    Nil  : forall ctxt. ExprList ctxt []

    (::) : forall ctxt, headT, tailT.
           (head    : Expr ctxt headT) ->
           (tail    : ExprList ctxt tailT) ->
           ExprList ctxt (headT :: tailT)


-- public export
-- data Args: forall len.
--            (ctxt  : Context) ->
--            (types : TypeVect len) ->
--            Type where

--   Comma : forall ctxt, types.
--           (args : ExprList ctxt types) ->
--           Args ctxt types

--   Many  : forall ctxt, t1, t2, ts.
--           (expr : MultivaluedExpr ctxt (t1 :: t2 :: ts)) ->
--           Args ctxt (t1 :: t2 :: ts)


public export
data Callable : forall ctxt, parTypes, retTypes.
                (expr : Expr ctxt (GoFunc $ parTypes `To` retTypes)) ->
                Type


public export
record Call (ctxt : Context) (retType : GoType) where
  constructor MkCall
  {parLen : Nat}
  {parTypes : TypeVect parLen}
  func : Expr ctxt (GoFunc $ parTypes `To` [retType])
  {auto 0 s : Callable func}
  args : ExprList ctxt parTypes


public export
onAnonFunc: {parLen, retLen : Nat} ->
            (ctxt     : Context) ->
            (parTypes : TypeVect parLen) ->
            (retTypes : TypeVect retLen) ->
            Context
onAnonFunc {parLen} ctxt newTypes retTypes =
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


namespace Expr
  data Expr : (ctxt : Context) -> (res : GoType) -> Type where
-- @WHEN HOLES
-- @    Hole       : forall ctxt, res. Expr ctxt res
-- @END HOLES

    AnonFunc    : forall ctxt, retTypes.
                  {parLen     : Nat} ->
                  {0 parTypes : TypeVect parLen} ->
                  (body       : Statement (onAnonFunc ctxt parTypes retTypes)) ->
                  Expr ctxt (GoFunc $ parTypes `To` retTypes)

    GetLiteral  : forall ctxt, resType.
                  (literal    : Literal resType) ->
                  Expr ctxt resType

-- @WHEN EXTRA_BUILTINS
-- @     ApplyPrefix : forall ctxt.
-- @                   {argType, resType : GoType} ->
-- @                   (op  : PrefixOp argType resType) ->
-- @                   (arg : Expr ctxt argType) ->
-- @                   Expr ctxt resType
-- @END EXTRA_BUILTINS

    -- ApplyInfix  : forall ctxt, resType.
    --               {lhvType, rhvType : GoType} ->
    --               (op  : InfixOp lhvType rhvType resType) ->
    --               (lhv : Expr ctxt lhvType) ->
    --               (rhv : Expr ctxt rhvType) ->
    --               Expr ctxt resType

    -- CallBuiltin : forall ctxt, retType.
    --               {parLen   : Nat} ->
    --               {parTypes : TypeVect parLen} ->
    --               (typePar  : MaybeType) ->
    --               (func : BuiltinFunc typePar parTypes [retType]) ->
    --               (args : ExprList ctxt parTypes) ->
    --               Expr ctxt retType

    CallNormal  : forall ctxt, retType.
                  (call : Call ctxt retType) ->
                  Expr ctxt retType

    GetDecl     : forall ctxt, type.
                  (idx : Fin ctxt.stackLen) ->
                  (0 bt : ByType type ctxt.stack idx) =>
                  Expr ctxt type


-- namespace MultivaluedExpr
--   data MultivaluedExpr : forall len.
--                          (ctxt : Context) ->
--                          (res : TypeVect len) ->
--                          Type where

--     Call        : forall ctxt, retTypes.
--                   {parLen   : Nat} ->
--                   {parTypes : TypeVect parLen} ->
--                   (func : Expr ctxt (GoFunc $ parTypes `To` retTypes)) ->
--                   (0 s : Callable func) =>
--                   (args : Args ctxt parTypes) ->
--                   MultivaluedExpr ctxt retTypes


data Callable : forall ctxt, parTypes, retTypes.
                (expr : Expr ctxt (GoFunc $ parTypes `To` retTypes)) ->
                Type where

  FromFuncLiteral : forall ctxt, parTypes, retTypes.
                    (body : Statement (onAnonFunc ctxt parTypes retTypes)) ->
                    Callable {ctxt} {parTypes} {retTypes} (AnonFunc body)

  FromGetDecl     : forall ctxt, parTypes, retTypes.
                    (idx   : Fin ctxt.stackLen) ->
                    (0 br  : ByRet parTypes retTypes ctxt.stack idx) =>
                    Callable {ctxt} (GetDecl idx @{byRetToByType br})


namespace MaybeCont
  public export
  data MaybeCont : (isTerm : Bool) -> (newCtxt : Context) -> Type where
    Just    : forall ctxt. (cont : Statement ctxt) -> MaybeCont False ctxt
    Nothing : forall ctxt. MaybeCont True ctxt


-- @WHEN IF_STMTS
-- @ public export
-- @ data IfTerm : (isIfTerm, isThenTerm, isElseTerm : Bool) -> Type where
-- @   TTT : IfTerm True True True
-- @   FAA : forall th, el. IfTerm False th el


-- @END IF_STMTS


public export
onDeclare : {count    : Nat} ->
            (ctxt     : Context) ->
            (kind     : Kind) ->
            (newTypes : TypeVect count) ->
            Context
onDeclare ctxt kind newTypes =
  { stackLen   $= (+ count)
  , stack      $= push kind newTypes
  , blockDepth := rewrite plusCommutative ctxt.stackLen count in
                    rewrite plusSuccRightSucc count ctxt.stackLen in
                      shift count ctxt.blockDepth
  } ctxt


data Statement : (ctxt : Context) -> Type where
  JustStop    : forall ctxt.
                (0 nt : BoolEqual ctxt.isTerminating False) =>
                Statement ctxt

  Return      : forall ctxt.
                (0 term : BoolEqual ctxt.isTerminating True) =>
                (res    : ExprList ctxt ctxt.returns) ->
                Statement ctxt

  -- Var         : forall ctxt.
  --               {count'   : Nat} ->
  --               (newTypes : TypeVect (S count')) ->
  --               (initial  : Args ctxt newTypes) ->
  --               (cont     : Statement (onDeclare ctxt Var newTypes)) ->
  --               Statement ctxt

  -- Void        : forall ctxt.
  --               (value : MultivaluedExpr ctxt []) ->
  --               (cont  : Statement ctxt) ->
  --               Statement ctxt

  -- @WHEN IF_STMTS
-- @   If          : forall ctxt.
-- @                 {tt, et : Bool} ->
-- @                 (0 term : IfTerm ctxt.isTerminating tt et) =>
-- @                 (test  : Expr ctxt GoBool) ->
-- @                 (then_ : Statement $ setIsTerminating tt ctxt) ->
-- @                 (else_ : Statement $ setIsTerminating et ctxt) ->
-- @                 (cont  : MaybeCont ctxt.isTerminating ctxt) ->
-- @                 Statement ctxt
-- @END IF_STMTS

  -- ChanSend    : forall ctxt.
  --               {type  : GoType} ->
  --               (chan  : Expr ctxt (GoChan type)) ->
  --               (value : Expr ctxt (type)) ->
  --               (cont  : Statement ctxt) ->
  --               Statement ctxt

  -- ChanSpecVar : forall ctxt.
  --               {type    : GoType} ->
  --               (initial : Expr ctxt (GoChan type)) ->
  --               (cont    : Statement (onDeclare ctxt Var [type, GoBool])) ->
  --               Statement ctxt

  -- Go          : forall ctxt.
  --               {retLen, parLen : Nat} ->
  --               {retTypes : TypeVect retLen} ->
  --               {parTypes : TypeVect parLen} ->
  --               (func : Expr ctxt (GoFunc $ parTypes `To` retTypes)) ->
  --               (0 s : Callable func) =>
  --               (args : Args ctxt parTypes) ->
  --               (cont : Statement ctxt) ->
  --               Statement ctxt


export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs : Fuel -> (ctxt : Context) -> (ret : GoType) ->
           Gen MaybeEmpty $ Expr ctxt ret
