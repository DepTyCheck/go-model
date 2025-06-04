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

namespace MaybeType
  public export
  data MaybeType = Just GoType | Nothing

public export
record GoFuncType where
  constructor To
  {parLen : Nat}
  par : TypeVect parLen
  ret : MaybeType

data GoType : Type where
  GoInt  : GoType
  GoBool : GoType
  GoFunc : GoFuncType -> GoType
  GoChan : GoType -> GoType

export
Biinjective TypeVect.(::) where
  biinjective Refl = (Refl, Refl)

export
Injective MaybeType.Just where
  injective Refl = Refl

export
Injective GoFunc where
  injective Refl = Refl

export
Injective GoChan where
  injective Refl = Refl


export
{0 len : Nat} -> DecEq (TypeVect len)

export
DecEq MaybeType

export
DecEq GoFuncType

export
DecEq GoType where
  decEq GoInt      GoInt       = Yes Refl
  decEq GoBool     GoBool      = Yes Refl
  decEq (GoFunc f) (GoFunc f') = decEqCong (decEq f f')
  decEq (GoChan t) (GoChan t') = decEqCong (decEq t t')
  decEq GoInt      GoBool      = No $ \case Refl impossible
  decEq GoInt      (GoFunc _)  = No $ \case Refl impossible
  decEq GoInt      (GoChan _)  = No $ \case Refl impossible
  decEq GoBool     GoInt       = No $ \case Refl impossible
  decEq GoBool     (GoFunc _)  = No $ \case Refl impossible
  decEq GoBool     (GoChan _)  = No $ \case Refl impossible
  decEq (GoFunc _) GoInt       = No $ \case Refl impossible
  decEq (GoFunc _) GoBool      = No $ \case Refl impossible
  decEq (GoFunc _) (GoChan _)  = No $ \case Refl impossible
  decEq (GoChan _) GoInt       = No $ \case Refl impossible
  decEq (GoChan _) GoBool      = No $ \case Refl impossible
  decEq (GoChan _) (GoFunc _)  = No $ \case Refl impossible

{0 len : Nat} -> DecEq (TypeVect len) where
  decEq Nil Nil = Yes Refl
  decEq (t1 :: ts1) (t2 :: ts2) =
    assert_total decEqCong2 (decEq t1 t2) (decEq ts1 ts2)

DecEq MaybeType where
  decEq (Just t1) (Just t2) = assert_total decEqCong (decEq t1 t2)
  decEq (Just _) Nothing = No $ \case Refl impossible
  decEq Nothing (Just _) = No $ \case Refl impossible
  decEq Nothing Nothing = Yes Refl

DecEq GoFuncType where
  decEq (To {parLen} par ret) (To {parLen = parLen'} par' ret') =
      let Yes Refl  := decEq parLen parLen'
            | No contra => No $ \eq => contra $ fst $ injDP eq
          Yes parEq := decEq par par'
            | No contra => No $ \eq => contra $ fst $ snd $ injDP eq
          Yes retEq := decEq ret ret'
            | No contra => No $ \eq => contra $ snd $ snd $ injDP eq
       in Yes $ congDP parEq retEq

    where
      congDP : forall par, par', ret, ret'.
               (0 _ : (par = par')) ->
               (0 _ : (ret = ret')) ->
               (To par ret = To par' ret')
      congDP Refl Refl = Refl

      injDP : forall parLen, parLen'.
              {0 par  : TypeVect parLen} ->
              {0 par' : TypeVect parLen'} ->
              {0 ret  : MaybeType} ->
              {0 ret' : MaybeType} ->
              (0 _    : (To par ret = To par' ret')) ->
              (parLen = parLen', par = par', ret = ret')
      injDP Refl = (Refl, Refl, Refl)

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
data ByRet : forall len, parLen.
             (par : TypeVect parLen) ->
             (ret : MaybeType) ->
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
data ByElem : forall len.
              (elemType : GoType) ->
              (stack : Stack len) ->
              (idx : Fin len) ->
              Type where

  HereE  : forall elemType, kind, tail.
           ByElem elemType (tail :< MkDecl kind (GoChan elemType)) FZ

  ThereE : forall elemType, head, tail, found.
           (there : ByElem elemType tail found) ->
           ByElem elemType (tail :< head) (FS found)


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
  returns       : MaybeType
  isTerminating : Bool

public export
setIsTerminating : Bool -> Context -> Context
setIsTerminating value = { isTerminating := value }


public export
data Statement : (ctxt : Context) -> Type

namespace Expr
  public export
  data Expr : (ctxt : Context) -> (res : GoType) -> Type


public export
record GetChanDecl (ctxt : Context) (elemType : GoType) where
  constructor ChanAt
  idx : Fin ctxt.stackLen
  {auto 0 be : ByElem elemType ctxt.stack idx}


public export
data Literal : (ty : GoType) -> Type where
  MkInt  : Nat  -> Literal GoInt
  MkBool : Bool -> Literal GoBool


public export
data BuiltinFunc : (ctxt : Context) -> (retType : GoType) -> Type where

  IntAdd : forall ctxt. (lhv, rhv : Expr ctxt GoInt) -> BuiltinFunc ctxt GoInt

  ChanLen : forall ctxt, elemType.
            (chan : GetChanDecl ctxt elemType) ->
            BuiltinFunc ctxt GoInt

-- @WHEN EXTRA_BUILTINS
-- @   BoolNot  : PrefixOp GoBool GoBool
-- @   IntNeg   : PrefixOp GoInt GoInt
-- @END EXTRA_BUILTINS

  -- @WHEN EXTRA_BUILTINS
-- @   IntSub, IntMul  : InfixOp GoInt GoInt GoInt
-- @   BoolAnd, BoolOr : InfixOp GoBool GoBool GoBool
-- @   IntEq, IntNE, IntLt, IntLE, IntGt, IntGE : InfixOp GoInt GoInt GoBool
  -- @END EXTRA_BUILTINS

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


namespace MaybeExpr
  public export
  data MaybeExpr : (ctxt : Context) -> (type : MaybeType) -> Type where
    Just : forall ctxt, inner. Expr ctxt inner -> MaybeExpr ctxt (Just inner)
    Nothing : forall ctxt. MaybeExpr ctxt Nothing


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
data Callable : forall ctxt, parTypes, retType.
                (expr : Expr ctxt (GoFunc $ parTypes `To` retType)) ->
                Type


public export
record Call (ctxt : Context) (retType : MaybeType) where
  constructor MkCall
  {parLen : Nat}
  {parTypes : TypeVect parLen}
  func : Expr ctxt (GoFunc $ parTypes `To` retType)
  {auto 0 s : Callable func}
  args : ExprList ctxt parTypes



public export
onAnonFunc: {parLen : Nat} ->
            (ctxt : Context) ->
            (parTypes : TypeVect parLen) ->
            (retType : MaybeType) ->
            Context
onAnonFunc {parLen} ctxt newTypes retType =
  { stackLen      $= (+ parLen)
  , stack         $= push Var newTypes
  , blockDepth    := natToFinLT @{prf parLen ctxt.stackLen} parLen
  , returns       := retType
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

    ELambda     : forall ctxt.
                  {parLen : Nat} ->
                  {parTypes : TypeVect parLen} ->
                  {retType : MaybeType} ->
                  (body : Statement (onAnonFunc ctxt parTypes retType)) ->
                  Expr ctxt (GoFunc $ parTypes `To` retType)

    ELiteral    : forall ctxt, resType.
                  (literal : Literal resType) ->
                  Expr ctxt resType

    EBuiltin    : forall ctxt, retType.
                  (func : BuiltinFunc ctxt retType) ->
                  Expr ctxt retType

    ECall       : forall ctxt, retType.
                  (call : Call ctxt (Just retType)) ->
                  Expr ctxt retType

    EGetDecl    : forall ctxt, type.
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


data Callable : forall ctxt, parTypes, retType.
                (expr : Expr ctxt (GoFunc $ parTypes `To` retType)) ->
                Type where

  FromFuncLiteral : forall ctxt, parTypes, retType.
                    (body : Statement (onAnonFunc ctxt parTypes retType)) ->
                    Callable {ctxt} {parTypes} {retType} (ELambda body)

  FromGetDecl     : forall ctxt, parTypes, retTypes.
                    (idx   : Fin ctxt.stackLen) ->
                    (0 br  : ByRet parTypes retTypes ctxt.stack idx) =>
                    Callable {ctxt} (EGetDecl idx @{byRetToByType br})


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


-- public export
-- data ChanBuf : (ctxt : Context) -> Type where
--   Buffered : forall ctxt. (cap : Expr ctxt GoInt) -> ChanBuf ctxt
--   Unbuffered : forall ctxt. ChanBuf ctxt


public export
data ChanOp : (ctxt : Context) -> Type where
  Open    : forall ctxt.
            {elemType : GoType} ->
            -- (chanBuf : ChanBuf ctxt) ->
            (cap : Expr ctxt GoInt) ->
            ChanOp ctxt

  Send    : forall ctxt, elemType.
            (chan  : GetChanDecl ctxt elemType) ->
            (value : Expr ctxt elemType) ->
            ChanOp ctxt

  Recv    : forall ctxt.
            (varCount : Fin 3) ->
            {elemType : GoType} ->
            (chan  : GetChanDecl ctxt elemType) ->
            ChanOp ctxt


public export
onChanOp : (ctxt : Context) -> (op : ChanOp ctxt) -> Context
onChanOp ctxt (Open {elemType} _) = onDeclare ctxt Var [GoChan elemType]
onChanOp ctxt (Send _ _) = ctxt
onChanOp ctxt (Recv 0 _)  = ctxt
onChanOp ctxt (Recv 1 {elemType} _) = onDeclare ctxt Var [elemType]
onChanOp ctxt (Recv 2 {elemType} _) = onDeclare ctxt Var [elemType, GoBool]


data Statement : (ctxt : Context) -> Type where
  SStop       : forall ctxt.
                (0 nt : BoolEqual ctxt.isTerminating False) =>
                Statement ctxt

  SReturn     : forall ctxt.
                (0 term : BoolEqual ctxt.isTerminating True) =>
                (res : MaybeExpr ctxt ctxt.returns) ->
                Statement ctxt

  SPrintLn    : forall ctxt.
                {argType : GoType} ->
                (arg : Expr ctxt argType) ->
                (cont : Statement ctxt) ->
                Statement ctxt

  SVar1       : forall ctxt.
                {newType : GoType} ->
                (initial : Expr ctxt newType) ->
                (cont    : Statement (onDeclare ctxt Var [newType])) ->
                Statement ctxt

  SCall       : forall ctxt.
                {retType : MaybeType} ->
                (async : Bool) ->
                (call : Call ctxt retType) ->
                (cont : Statement ctxt) ->
                Statement ctxt

  SChanOp   : forall ctxt.
                (op : ChanOp ctxt) ->
                (cont : Statement (onChanOp ctxt op)) ->
                Statement ctxt


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

export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt
