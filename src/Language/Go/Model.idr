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


namespace TypeVect
  public export
  replicate : (len : Nat) -> (type : Scalar) -> TypeVect len
  replicate 0 _ = []
  replicate (S len') type = type :: replicate len' type


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
  name : Nat
  type : GType


namespace Stack
  public export
  data Stack : (len : Nat) -> Type where
    Lin  : Stack Z
    (:<) : forall len. Stack len -> Decl -> Stack (S len)


public export
push1 : forall len. Kind -> Nat -> GType -> Stack len -> Stack (S len)
push1 kind name type stack = stack :< MkDecl kind name type

public export
push : forall len, count.
       Kind ->
       Nat ->
       TypeVect count ->
       Stack len ->
       Stack (len + count)
push _ _ [] stack = rewrite plusZeroRightNeutral len in stack
push {len} {count = S count'} kind name (t :: ts) stack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind (S name) ts $ stack :< MkDecl kind name (GS t)


public export
data ByType : forall len. GType -> Stack len -> Fin len -> Type where
  HereT  : forall ty, name, kind, tail.
           ByType ty (tail :< MkDecl kind name ty) FZ

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

  HereR  : forall par, ret, kind, name, tail.
           ByRet
             par ret
             (tail :< MkDecl kind name (GFunc $ par `To` ret))
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

  HereE  : forall elemType, kind, name, tail.
           ByElem elemType (tail :< MkDecl kind name (GChan elemType)) FZ

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


namespace Block
  public export
  data Block : (cnt : Nat) -> (ctxt : Context) -> (isTerm : Bool) -> Type


  public export
  tick : forall ctxt, isTerm. {cnt : Nat} -> Block cnt ctxt isTerm -> Nat


namespace Expr
  public export
  data Expr : (cnt : Nat) -> (ctxt : Context) -> (res : GType) -> Type


  public export
  tick : forall ctxt, ret. {cnt : Nat} -> Expr cnt ctxt ret -> Nat


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
                  (cnt : Nat) ->
                  (ctxt  : Context) ->
                  (types : TypeVect len) ->
                  Type where

    Nil  : forall cnt, ctxt. ExprList cnt ctxt []

    (::) : forall cnt, ctxt, headT, tailT.
           (head : Expr cnt ctxt (GS headT)) ->
           (tail : ExprList (tick head) ctxt tailT) ->
           ExprList cnt ctxt (headT :: tailT)


  public export
  tick : forall ctxt, types. {cnt : Nat} -> ExprList cnt ctxt types -> Nat
  tick {cnt} Nil = cnt
  tick (head :: tail) = tick tail


namespace ExprHList
  public export
  data ExprHList : (cnt : Nat) ->
                   (ctxt  : Context) ->
                   (type : GType) ->
                   Type where

    Nil  : forall cnt, ctxt, type. ExprHList cnt ctxt type

    (::) : forall cnt, ctxt, type.
           (head : Expr cnt ctxt type) ->
           (tail : ExprHList (tick head) ctxt type) ->
           ExprHList cnt ctxt type


  public export
  tick : forall ctxt, type. {cnt : Nat} -> ExprHList cnt ctxt type -> Nat
  tick {cnt} Nil = cnt
  tick (head :: tail) = tick tail


namespace MaybeExpr
  public export
  data MaybeExpr : (cnt : Nat) -> (ctxt : Context) -> (type : MaybeType) -> Type where

    Just : forall cnt, ctxt, inner.
           Expr cnt ctxt (GS inner) ->
           MaybeExpr cnt ctxt (Just inner)

    Nothing : forall cnt, ctxt. MaybeExpr cnt ctxt Nothing


  public export
  tick : forall ctxt, type. {cnt : Nat} -> MaybeExpr cnt ctxt type -> Nat
  tick (Just expr) = tick expr
  tick {cnt} Nothing = cnt


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
data Callable : forall cnt, ctxt, parTypes, retType.
                (expr : Expr cnt ctxt (GFunc $ parTypes `To` retType)) ->
                Type


namespace Call
  public export
  record Call (cnt : Nat) (ctxt : Context) (retType : MaybeType) where
    constructor MkCall
    {parLen : Nat}
    {parTypes : TypeVect parLen}
    func : Expr cnt ctxt (GFunc $ parTypes `To` retType)
    {auto 0 s : Callable func}
    args : ExprList (tick func) ctxt parTypes


  public export
  tick : forall ctxt, ret. {cnt : Nat} -> Call cnt ctxt ret -> Nat
  tick (MkCall func args) = tick args


public export
lambdaCnt : (cnt : Nat) ->
            {parLen : Nat} ->
            (parTypes : TypeVect parLen) ->
            Nat
lambdaCnt cnt {parLen} _ = cnt + parLen

public export
lambdaCtxt : {parLen : Nat} ->
             (cnt : Nat) ->
             (ctxt : Context) ->
             (parTypes : TypeVect parLen) ->
             (retType : MaybeType) ->
             Context
lambdaCtxt {parLen} cnt ctxt newTypes retType =
  { stackLen      $= (+ parLen)
  , stack         $= push Var cnt newTypes
  , blockDepth    := natToFinLT @{prf parLen ctxt.stackLen} parLen
  , returns       := retType
  } ctxt

  where
    0 prf : (0 a, b : Nat) -> LT a (S $ b + a)
    prf a b = rewrite plusCommutative b a in
                LTESucc $ lteAddRight {m = b} a


namespace Expr
  data Expr : (cnt : Nat) -> (ctxt : Context) -> (res : GType) -> Type where
-- @WHEN HOLES
-- @    Hole       : forall ctxt, res. Expr ctxt res
-- @END HOLES

    ELambda : forall cnt, ctxt.
              {parLen : Nat} ->
              {parTypes : TypeVect parLen} ->
              {retType : MaybeType} ->
              (body : Block (lambdaCnt cnt parTypes)
                            (lambdaCtxt cnt ctxt parTypes retType)
                            True) ->
              Expr cnt ctxt (GFunc $ parTypes `To` retType)

    ELiteral    : forall cnt, ctxt, resType.
                  (literal : Literal resType) ->
                  Expr cnt ctxt (GS resType)

    -- EUnary      : forall cnt, ctxt, retType.
    --               {argType : Scalar} ->
    --               (func : Unary argType retType) ->
    --               (arg : Expr ctxt (GS argType)) ->
    --               Expr cnt ctxt (GS retType)

    -- EBinary     : forall cnt, ctxt, retType.
    --               {lhvType, rhvType : Scalar} ->
    --               (func : Binary lhvType rhvType retType) ->
    --               (lhv : Expr ctxt (GS lhvType)) ->
    --               (rhv : Expr (tick lhv) (GS rhvType)) ->
    --               Expr cnt ctxt (GS retType)

    ECall       : forall cnt, ctxt, retType.
                  (call : Call cnt ctxt (Just retType)) ->
                  Expr cnt ctxt (GS retType)

    EGetDecl    : forall cnt, ctxt, type.
                  (idx : Fin ctxt.stackLen) ->
                  (0 bt : ByType type ctxt.stack idx) =>
                  Expr cnt ctxt type


  tick (ELambda body) = tick body
  tick {cnt} (ELiteral _) = cnt
  tick (ECall call) = tick call
  tick {cnt} (EGetDecl idx) = cnt


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


data Callable : forall cnt, ctxt, parTypes, retType.
                (expr : Expr cnt ctxt (GFunc $ parTypes `To` retType)) ->
                Type where

  FromFuncLiteral : forall cnt, ctxt, parTypes, retType.
                    (body : Block (lambdaCnt cnt parTypes)
                                  (lambdaCtxt cnt ctxt parTypes retType)
                                  True) ->
                    Callable {cnt} {ctxt} {parTypes} {retType} (ELambda body)

  FromGetDecl     : forall ctxt, parTypes, retTypes.
                    (idx   : Fin ctxt.stackLen) ->
                    (0 br  : ByRet parTypes retTypes ctxt.stack idx) =>
                    Callable {ctxt} (EGetDecl idx @{byRetToByType br})


-- @WHEN IF_STMTS
public export
data IfTerm : (isIfTerm, isThenTerm, isElseTerm : Bool) -> Type where
  TTT : IfTerm True True True
  FFT : forall el. IfTerm False False el
  FTF : forall th. IfTerm False th False
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
decl1Cnt : (cnt : Nat) -> Nat
decl1Cnt cnt = S cnt

public export
decl1Ctxt : (cnt : Nat) ->
            (ctxt : Context) ->
            (kind : Kind) ->
            (newType : GType) ->
            Context
decl1Ctxt cnt ctxt kind newType =
  { stackLen   $= S
  , stack      $= push1 kind cnt newType
  , blockDepth $= FS
  } ctxt


-- public export
-- data ChanBuf : (ctxt : Context) -> Type where
--   Buffered : forall ctxt. (cap : Expr ctxt GInt) -> ChanBuf ctxt
--   Unbuffered : forall ctxt. ChanBuf ctxt


namespace ChanOp
  public export
  data ChanOp : (cnt : Nat) -> (ctxt : Context) -> Type where
    Open    : forall cnt, ctxt.
              (elemType : Scalar) ->
              (cap : Expr cnt ctxt (GS GInt)) ->
              ChanOp cnt ctxt

    Send    : forall cnt, ctxt.
              {elemType : Scalar} ->
              (chan  : GetChanDecl ctxt elemType) ->
              (value : Expr cnt ctxt (GS elemType)) ->
              ChanOp cnt ctxt

    Recv    : forall cnt, ctxt.
              {elemType : Scalar} ->
              (chan : GetChanDecl ctxt elemType) ->
              ChanOp cnt ctxt


  public export
  openName : {cnt : _} -> forall ctxt. (cap : Expr cnt ctxt (GS GInt)) -> Nat
  openName cap = tick cap

  public export
  recvName1 : (cnt : Nat) -> Nat
  recvName1 cnt = cnt


  public export
  tick : forall ctxt. {cnt : Nat} -> ChanOp cnt ctxt -> Nat
  tick (Open _ cap) = tick cap + 1
  tick (Send chan value) = tick value + 1
  tick {cnt} (Recv chan) = cnt + 2


  public export
  chanOpCtxt : {cnt : _} -> {ctxt : _} -> (op : ChanOp cnt ctxt) -> Context
  chanOpCtxt {ctxt} (Open elemType cap) =
    decl1Ctxt (openName cap) ctxt Var (GChan elemType)
  chanOpCtxt {ctxt} (Send _ _) = ctxt
  chanOpCtxt {ctxt} (Recv {elemType} chan) =
    let name := recvName1 cnt
        ctxt' := decl1Ctxt name ctxt Var $ GS elemType
    in decl1Ctxt (S name) ctxt' Var (GS GBool)


namespace Stmt
  public export
  data Stmt : (cnt : Nat) -> (ctxt : Context) -> (isTerm : Bool) -> Type where
    SReturn : forall cnt, ctxt.
              (res : MaybeExpr cnt ctxt ctxt.returns) ->
              Stmt cnt ctxt True

    SChanOp : forall cnt, ctxt.
              (op : ChanOp cnt ctxt) ->
              Stmt cnt ctxt False

    SVar1 : forall cnt, ctxt.
            {newType : GType} ->
            (initial : Expr cnt ctxt newType) ->
            Stmt cnt ctxt False

    SCall : forall cnt, ctxt.
            {retType : MaybeType} ->
            (async : Bool) ->
            (call : Call cnt ctxt retType) ->
            Stmt cnt ctxt False

  -- @WHEN IF_STMTS
    SIf : forall cnt, ctxt, isTerm.
          {tt, et : Bool} ->
          (branch : IfTerm isTerm tt et) =>
          (test : Expr cnt ctxt (GS GBool)) ->
          (then_ : Block (tick test) ctxt tt) ->
          (else_ : Block (tick then_) ctxt et) ->
          Stmt cnt ctxt isTerm
  -- @END IF_STMTS

    SLoop : forall cnt, ctxt.
            (elemType : Scalar) ->
            (elems : ExprHList cnt ctxt (GS elemType)) ->
            (body : Block (tick elems + 1)
                          (decl1Ctxt (tick elems) ctxt Var (GS elemType))
                          False) ->
            Stmt cnt ctxt False


  public export
  tick : forall ctxt, isTerm. {cnt : Nat} -> Stmt cnt ctxt isTerm -> Nat
  tick (SReturn res) = tick res
  tick (SChanOp op) = tick op
  tick (SVar1 initial) = tick initial + 1
  tick (SCall async call) = tick call
  tick (SIf test then_ else_) = tick else_
  tick (SLoop _ elems body) = tick body


  public export
  stmtCtxt : forall isTerm. {cnt : _} -> {ctxt : _} -> Stmt cnt ctxt isTerm -> Context
  stmtCtxt {ctxt} (SVar1 {newType} initial) = decl1Ctxt (tick initial) ctxt Var newType
  stmtCtxt {ctxt} (SChanOp op) = chanOpCtxt op
  stmtCtxt {ctxt} _ = ctxt


namespace Block
  data Block : (cnt : Nat) -> (ctxt : Context) -> (isTerm : Bool) -> Type where
    End : forall cnt, ctxt. Block cnt ctxt False

    Term : forall cnt, ctxt.
           (last : Stmt cnt ctxt True) ->
           Block cnt ctxt True

    Seq : forall cnt, ctxt, isTerm.
          (head : Stmt cnt ctxt False) ->
          (tail : Block (tick head) (stmtCtxt head) isTerm) ->
          Block cnt ctxt isTerm

  tick {cnt} End = cnt
  tick (Term last) = tick last
  tick (Seq head tail) = tick tail


export
genBlocks : Fuel -> (cnt : Nat) -> (ctxt : Context) -> (isTerm : Bool) ->
              Gen MaybeEmpty $ Block cnt ctxt isTerm
