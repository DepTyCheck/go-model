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


------------------------------------------------------------
--                    Typing
------------------------------------------------------------


public export
data Scalar = GInt | GBool


namespace MaybeType
  public export
  data MaybeType = Just Scalar | Nothing


namespace TypeVect
  public export
  data TypeVect : (len : Nat) -> Type where
    Nil  : TypeVect 0
    (::) : forall len. Scalar -> TypeVect len -> TypeVect (S len)


public export
record GFuncType where
  constructor To
  {parLen : Nat}
  par : TypeVect parLen
  ret : MaybeType


public export
data GType : Type where
  GS : Scalar -> GType
  GFunc : GFuncType -> GType
  GChan : Scalar -> GType


export
Biinjective TypeVect.(::) where
  biinjective Refl = (Refl, Refl)

export
Injective MaybeType.Just where
  injective Refl = Refl

export
Injective GS where
  injective Refl = Refl

export
Injective GFunc where
  injective Refl = Refl

export
Injective GChan where
  injective Refl = Refl


export
DecEq Scalar where
  decEq GInt  GInt  = Yes Refl
  decEq GBool GBool = Yes Refl
  decEq GInt  GBool = No $ \case Refl impossible
  decEq GBool GInt  = No $ \case Refl impossible

export
{0 len : Nat} -> DecEq (TypeVect len) where
  decEq Nil Nil = Yes Refl
  decEq (t1 :: ts1) (t2 :: ts2) =
    assert_total decEqCong2 (decEq t1 t2) (decEq ts1 ts2)

export
DecEq MaybeType where
  decEq (Just t1) (Just t2) = assert_total decEqCong (decEq t1 t2)
  decEq (Just _) Nothing = No $ \case Refl impossible
  decEq Nothing (Just _) = No $ \case Refl impossible
  decEq Nothing Nothing = Yes Refl

export
DecEq GFuncType where
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

export
DecEq GType where
  decEq (GS s1) (GS s2) = decEqCong (decEq s1 s2)
  decEq (GFunc f) (GFunc f') = decEqCong (decEq f f')
  decEq (GChan t) (GChan t') = decEqCong (decEq t t')
  decEq (GS _) (GFunc _) = No $ \case Refl impossible
  decEq (GS _) (GChan _) = No $ \case Refl impossible
  decEq (GFunc _) (GS _)    = No $ \case Refl impossible
  decEq (GFunc _) (GChan _) = No $ \case Refl impossible
  decEq (GChan _) (GS _)    = No $ \case Refl impossible
  decEq (GChan _) (GFunc _) = No $ \case Refl impossible

-- data IsEmpty : forall len. TypeVect len -> Type where
--   [search len]
--   ItIsEmpty : IsEmpty []


-- data NonEmpty : forall len. TypeVect len -> Type where
--   [search len]
--   IsNonEmpty : forall head, tail. NonEmpty (head :: tail)


public export
data Kind
  = Var
  | Const
  | Func

public export
record Decl where
  constructor MkDecl
  kind : Kind
  type : GType


namespace Stack
  public export
  data Stack : (len : Nat) -> Type where
    Lin  : Stack Z
    (:<) : forall len. Stack len -> Decl -> Stack (S len)


push1 : forall len. Kind -> GType -> Stack len -> Stack (S len)
push1 kind t stack = stack :< MkDecl kind t

push : forall len, count.
       Kind ->
       TypeVect count ->
       Stack len ->
       Stack (len + count)
push _ [] stack = rewrite plusZeroRightNeutral len in stack
push {len} {count = S count'} kind (t :: ts) stack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind ts $ stack :< MkDecl kind (GS t)


public export
data ByType : forall len. GType -> Stack len -> Fin len -> Type where
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
           ByRet
             par ret
             (tail :< MkDecl kind (GFunc $ par `To` ret))
             FZ

  ThereR : forall par, ret, head, tail, found.
           (there : ByRet par ret tail found) ->
           ByRet par ret (tail :< head) (FS found)

public export
data ByElem : forall len.
              (elemType : Scalar) ->
              (stack : Stack len) ->
              (idx : Fin len) ->
              Type where

  HereE  : forall elemType, kind, tail.
           ByElem elemType (tail :< MkDecl kind (GChan elemType)) FZ

  ThereE : forall elemType, head, tail, found.
           (there : ByElem elemType tail found) ->
           ByElem elemType (tail :< head) (FS found)


public export
byRetToByType : forall par, ret, stack, idx.
                ByRet par ret stack idx ->
                ByType (GFunc $ par `To` ret) stack idx
byRetToByType HereR = HereT
byRetToByType (ThereR there) = ThereT (byRetToByType there)


public export
record Context where
  constructor MkContext
  stackLen      : Nat
  stack         : Stack stackLen
  blockDepth    : Fin (S stackLen)
  returns       : MaybeType


public export
data Stmt : (ctxt : Context) -> (isTerm : Bool) -> Type

namespace Expr
  public export
  data Expr : (ctxt : Context) -> (res : GType) -> Type


public export
record GetChanDecl (ctxt : Context) (elemType : Scalar) where
  constructor ChanAt
  idx : Fin ctxt.stackLen
  {auto 0 be : ByElem elemType ctxt.stack idx}


public export
data Literal : (ty : Scalar) -> Type where
  MkInt  : Nat  -> Literal GInt
  MkBool : Bool -> Literal GBool


public export
data Unary : (argType, resType : Scalar) -> Type where
  IntNeg : Unary GInt GInt

public export
data Binary : (lhvType, rhvType, resType : Scalar) -> Type where
  IntAdd : Binary GInt GInt GInt
  IntGE : Binary GInt GInt GBool

-- @WHEN EXTRA_BUILTINS
-- @  BoolNot : BuiltinFunc [GBool] GBool
-- @  IntSub, IntMul  : InfixOp GInt GInt GInt
-- @  BoolAnd, BoolOr : InfixOp GBool GBool GBool
-- @  IntEq, IntNE, IntLt, IntLE, IntGt, IntGE : InfixOp GInt GInt GBool
-- @END EXTRA_BUILTINS

  -- ChanLen : forall ctxt, elemType.
  --           (chan : GetChanDecl ctxt elemType) ->
  --           BuiltinFunc ctxt GInt

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
           (head : Expr ctxt (GS headT)) ->
           (tail : ExprList ctxt tailT) ->
           ExprList ctxt (headT :: tailT)


namespace MaybeExpr
  public export
  data MaybeExpr : (ctxt : Context) -> (type : MaybeType) -> Type where

    Just : forall ctxt, inner.
           Expr ctxt (GS inner) ->
           MaybeExpr ctxt (Just inner)

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
                (expr : Expr ctxt (GFunc $ parTypes `To` retType)) ->
                Type


public export
record Call (ctxt : Context) (retType : MaybeType) where
  constructor MkCall
  {parLen : Nat}
  {parTypes : TypeVect parLen}
  func : Expr ctxt (GFunc $ parTypes `To` retType)
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
  } ctxt

  where
    0 prf : (0 a, b : Nat) -> LT a (S $ b + a)
    prf a b = rewrite plusCommutative b a in
                LTESucc $ lteAddRight {m = b} a


namespace Expr
  data Expr : (ctxt : Context) -> (res : GType) -> Type where
-- @WHEN HOLES
-- @    Hole       : forall ctxt, res. Expr ctxt res
-- @END HOLES

    ELambda     : forall ctxt.
                  {parLen : Nat} ->
                  {parTypes : TypeVect parLen} ->
                  {retType : MaybeType} ->
                  (body : Stmt (onAnonFunc ctxt parTypes retType) True) ->
                  Expr ctxt (GFunc $ parTypes `To` retType)

    ELiteral    : forall ctxt, resType.
                  (literal : Literal resType) ->
                  Expr ctxt (GS resType)

    -- EUnary      : forall ctxt, retType.
    --               {argType : Scalar} ->
    --               (func : Unary argType retType) ->
    --               (arg : Expr ctxt (GS argType)) ->
    --               Expr ctxt (GS retType)

    -- EBinary     : forall ctxt, retType.
    --               {lhvType, rhvType : Scalar} ->
    --               (func : Binary lhvType rhvType retType) ->
    --               (lhv : Expr ctxt (GS lhvType)) ->
    --               (rhv : Expr ctxt (GS rhvType)) ->
    --               Expr ctxt (GS retType)

    ECall       : forall ctxt, retType.
                  (call : Call ctxt (Just retType)) ->
                  Expr ctxt (GS retType)

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
--                   (func : Expr ctxt (GFunc $ parTypes `To` retTypes)) ->
--                   (0 s : Callable func) =>
--                   (args : Args ctxt parTypes) ->
--                   MultivaluedExpr ctxt retTypes


data Callable : forall ctxt, parTypes, retType.
                (expr : Expr ctxt (GFunc $ parTypes `To` retType)) ->
                Type where

  FromFuncLiteral : forall ctxt, parTypes, retType.
                    (body : Stmt (onAnonFunc ctxt parTypes retType) True) ->
                    Callable {ctxt} {parTypes} {retType} (ELambda body)

  FromGetDecl     : forall ctxt, parTypes, retTypes.
                    (idx   : Fin ctxt.stackLen) ->
                    (0 br  : ByRet parTypes retTypes ctxt.stack idx) =>
                    Callable {ctxt} (EGetDecl idx @{byRetToByType br})


-- @WHEN IF_STMTS
public export
data IfTerm : (isIfTerm, isThenTerm, isElseTerm : Bool) -> Type where
  TTT : IfTerm True True True
  FAA : forall th, el. IfTerm False th el
-- @END IF_STMTS

-- public export
-- onDeclare : {count    : Nat} ->
--             (ctxt     : Context) ->
--             (kind     : Kind) ->
--             (newTypes : TypeVect count) ->
--             Context
-- onDeclare ctxt kind newTypes =
--   { stackLen   $= (+ count)
--   , stack      $= push kind newTypes
--   , blockDepth := rewrite plusCommutative ctxt.stackLen count in
--                     rewrite plusSuccRightSucc count ctxt.stackLen in
--                       shift count ctxt.blockDepth
--   } ctxt

public export
onDeclare1 : (ctxt    : Context) ->
             (kind    : Kind) ->
             (newType : GType) ->
             Context
onDeclare1 ctxt kind newType =
  { stackLen   $= S
  , stack      $= push1 kind newType
  , blockDepth $= FS
  } ctxt


-- public export
-- data ChanBuf : (ctxt : Context) -> Type where
--   Buffered : forall ctxt. (cap : Expr ctxt GInt) -> ChanBuf ctxt
--   Unbuffered : forall ctxt. ChanBuf ctxt


public export
data ChanOp : (ctxt : Context) -> Type where
  Open    : forall ctxt.
            {elemType : Scalar} ->
            -- (chanBuf : ChanBuf ctxt) ->
            (cap : Expr ctxt (GS GInt)) ->
            ChanOp ctxt

  Send    : forall ctxt, elemType.
            (chan  : GetChanDecl ctxt elemType) ->
            (value : Expr ctxt (GS elemType)) ->
            ChanOp ctxt

  Recv    : forall ctxt.
            (varCount : Fin 3) ->
            {elemType : Scalar} ->
            (chan  : GetChanDecl ctxt elemType) ->
            ChanOp ctxt


public export
onChanOp : (ctxt : Context) -> (op : ChanOp ctxt) -> Context
onChanOp ctxt (Open {elemType} _) = onDeclare1 ctxt Var (GChan elemType)
onChanOp ctxt (Send _ _) = ctxt
onChanOp ctxt (Recv 0 _)  = ctxt
onChanOp ctxt (Recv 1 {elemType} _) = onDeclare1 ctxt Var (GS elemType)
onChanOp ctxt (Recv 2 {elemType} _) =
  onDeclare1 (onDeclare1 ctxt Var $ GS elemType) Var (GS GBool)


onStmt : forall isTerm. {ctxt : Context} -> Stmt ctxt isTerm -> Context


data Stmt : (ctxt : Context) -> (isTerm : Bool) -> Type where
  SReturn     : forall ctxt.
                (res : MaybeExpr ctxt ctxt.returns) ->
                Stmt ctxt True

  SNop        : forall ctxt.
                Stmt ctxt False

  SPrintLn    : forall ctxt.
                {argType : Scalar} ->
                (arg : Expr ctxt (GS argType)) ->
                Stmt ctxt False

  SVar1       : forall ctxt.
                {newType : GType} ->
                (initial : Expr ctxt newType) ->
                Stmt ctxt False

  SCall       : forall ctxt.
                {retType : MaybeType} ->
                (async : Bool) ->
                (call : Call ctxt retType) ->
                Stmt ctxt False

  -- SChanOp     : forall ctxt.
  --               (op : ChanOp ctxt) ->
  --               (cont : Stmt (onChanOp ctxt op)) ->
  --               Stmt ctxt

  SSeq        : forall ctxt, isTerm.
                (fst : Stmt ctxt False) ->
                (snd : Stmt (onStmt fst) isTerm) ->
                Stmt ctxt isTerm

  -- @WHEN IF_STMTS
  If          : forall ctxt, isTerm.
                {tt, et : Bool} ->
                (0 branch : IfTerm isTerm tt et) =>
                (test : Expr ctxt (GS GBool)) ->
                (then_ : Stmt ctxt tt) ->
                (else_ : Stmt ctxt et) ->
                Stmt ctxt isTerm
-- @END IF_STMTS


onStmt {ctxt} (SVar1 {newType} _) = onDeclare1 ctxt Var newType
onStmt {ctxt} (SSeq fst snd) = onStmt snd
onStmt {ctxt} _ = ctxt


export
genStmts : Fuel -> (ctxt : Context) -> (isTerm : Bool) ->
           Gen MaybeEmpty $ Stmt ctxt isTerm
