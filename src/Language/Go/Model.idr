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
data GType : (ord : Nat) -> Type

namespace TypeVect
  public export
  data TypeVect : (len : Nat) -> Type where
    Nil  : TypeVect 0
    (::) : forall len. GType 0 -> TypeVect len -> TypeVect (S len)

namespace MaybeType
  public export
  data MaybeType = Just (GType 0) | Nothing

public export
record GFuncType where
  constructor To
  {parLen : Nat}
  par : TypeVect parLen
  ret : MaybeType

data GType : (ord : Nat) -> Type where
  GInt  : GType 0
  GBool : GType 0
  GFunc : GFuncType -> GType 0
  GChan : forall ord. GType ord -> GType (S ord)


public export
record GTypeN where
  constructor GN
  {ord : Nat}
  snd : GType ord


export
Biinjective TypeVect.(::) where
  biinjective Refl = (Refl, Refl)

export
Injective MaybeType.Just where
  injective Refl = Refl

export
Injective GFunc where
  injective Refl = Refl

export
Injective GChan where
  injective Refl = Refl


test : forall ord. GType ord -> Nat
test GInt = 0
test GBool = 0
test (GFunc _) = 0
test (GChan c) = S (test c)

export
{0 len : Nat} -> DecEq (TypeVect len)

export
DecEq MaybeType

export
DecEq GFuncType

export
{0 ord : Nat} -> DecEq (GType ord) where
  decEq GInt      GInt       = Yes Refl
  decEq GBool     GBool      = Yes Refl
  decEq (GFunc f) (GFunc f') = decEqCong (decEq f f')
  decEq (GChan t) (GChan t') = decEqCong (decEq t t')
  decEq GInt      GBool      = No $ \case Refl impossible
  decEq GInt      (GFunc _)  = No $ \case Refl impossible
  decEq GBool     GInt       = No $ \case Refl impossible
  decEq GBool     (GFunc _)  = No $ \case Refl impossible
  decEq (GFunc _) GInt       = No $ \case Refl impossible
  decEq (GFunc _) GBool      = No $ \case Refl impossible

{0 len : Nat} -> DecEq (TypeVect len) where
  decEq Nil Nil = Yes Refl
  decEq (t1 :: ts1) (t2 :: ts2) =
    assert_total decEqCong2 (decEq t1 t2) (decEq ts1 ts2)

DecEq MaybeType where
  decEq (Just t1) (Just t2) = assert_total decEqCong (decEq t1 t2)
  decEq (Just _) Nothing = No $ \case Refl impossible
  decEq Nothing (Just _) = No $ \case Refl impossible
  decEq Nothing Nothing = Yes Refl

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
  type : GTypeN


namespace Stack
  public export
  data Stack : (len : Nat) -> Type where
    Lin  : Stack Z
    (:<) : forall len. Stack len -> Decl -> Stack (S len)


push1 : forall len. Kind -> GTypeN -> Stack len -> Stack (S len)
push1 kind t stack = stack :< MkDecl kind t

push : forall len, count.
       Kind ->
       TypeVect count ->
       Stack len ->
       Stack (len + count)
push _ [] stack = rewrite plusZeroRightNeutral len in stack
push {len} {count = S count'} kind (t :: ts) stack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind ts $ stack :< MkDecl kind (GN t)


public export
data ByType : forall len. GType 0 -> Stack len -> Fin len -> Type where
  HereT  : forall ty, kind, tail.
           ByType ty (tail :< MkDecl kind (GN ty)) FZ

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
             (tail :< MkDecl kind (GN $ GFunc $ par `To` ret))
             FZ

  ThereR : forall par, ret, head, tail, found.
           (there : ByRet par ret tail found) ->
           ByRet par ret (tail :< head) (FS found)

public export
data ByElem : forall len.
              (elemType : GType 0) ->
              (stack : Stack len) ->
              (idx : Fin len) ->
              Type where

  HereE  : forall elemType, kind, tail.
           ByElem elemType (tail :< MkDecl kind (GN $ GChan elemType)) FZ

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
  isTerminating : Bool

public export
setIsTerminating : Bool -> Context -> Context
setIsTerminating value = { isTerminating := value }


public export
data Statement : (ctxt : Context) -> Type

namespace Expr
  public export
  data Expr : (ctxt : Context) -> (res : GType 0) -> Type


public export
record GetChanDecl (ctxt : Context) (elemType : GType 0) where
  constructor ChanAt
  idx : Fin ctxt.stackLen
  {auto 0 be : ByElem elemType ctxt.stack idx}


public export
data Literal : (ty : GType 0) -> Type where
  MkInt  : Nat  -> Literal GInt
  MkBool : Bool -> Literal GBool


public export
data BuiltinFunc : forall len.
                   (paramTypes : TypeVect len) ->
                   (resType : GType 0) ->
                   Type where

  IntNeg : BuiltinFunc [GInt] GInt

  IntAdd : BuiltinFunc [GInt, GInt] GInt

  IntGE : BuiltinFunc [GInt, GInt] GBool

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
           (head : Expr ctxt headT) ->
           (tail : ExprList ctxt tailT) ->
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
  , isTerminating := True
  } ctxt

  where
    0 prf : (0 a, b : Nat) -> LT a (S $ b + a)
    prf a b = rewrite plusCommutative b a in
                LTESucc $ lteAddRight {m = b} a


namespace Expr
  data Expr : (ctxt : Context) -> (res : GType 0) -> Type where
-- @WHEN HOLES
-- @    Hole       : forall ctxt, res. Expr ctxt res
-- @END HOLES

    ELambda     : forall ctxt.
                  {parLen : Nat} ->
                  {parTypes : TypeVect parLen} ->
                  {retType : MaybeType} ->
                  (body : Statement (onAnonFunc ctxt parTypes retType)) ->
                  Expr ctxt (GFunc $ parTypes `To` retType)

    ELiteral    : forall ctxt, resType.
                  (literal : Literal resType) ->
                  Expr ctxt resType

    EBuiltin    : forall ctxt, argsLen, retType.
                  {argTypes : TypeVect argsLen} ->
                  (func : BuiltinFunc argTypes retType) ->
                  (args : ExprList ctxt argTypes) ->
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
--                   (func : Expr ctxt (GFunc $ parTypes `To` retTypes)) ->
--                   (0 s : Callable func) =>
--                   (args : Args ctxt parTypes) ->
--                   MultivaluedExpr ctxt retTypes


data Callable : forall ctxt, parTypes, retType.
                (expr : Expr ctxt (GFunc $ parTypes `To` retType)) ->
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
             (newType : GTypeN) ->
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
            {elemType : GType 0} ->
            -- (chanBuf : ChanBuf ctxt) ->
            (cap : Expr ctxt GInt) ->
            ChanOp ctxt

  Send    : forall ctxt, elemType.
            (chan  : GetChanDecl ctxt elemType) ->
            (value : Expr ctxt elemType) ->
            ChanOp ctxt

  Recv    : forall ctxt.
            (varCount : Fin 3) ->
            {elemType : GType 0} ->
            (chan  : GetChanDecl ctxt elemType) ->
            ChanOp ctxt


public export
onChanOp : (ctxt : Context) -> (op : ChanOp ctxt) -> Context
onChanOp ctxt (Open {elemType} _) = onDeclare1 ctxt Var (GN $ GChan elemType)
onChanOp ctxt (Send _ _) = ctxt
onChanOp ctxt (Recv 0 _)  = ctxt
onChanOp ctxt (Recv 1 {elemType} _) = onDeclare1 ctxt Var (GN elemType)
onChanOp ctxt (Recv 2 {elemType} _) =
  onDeclare1 (onDeclare1 ctxt Var $ GN elemType) Var (GN GBool)


data Statement : (ctxt : Context) -> Type where
  SStop       : forall ctxt.
                (0 nt : BoolEqual ctxt.isTerminating False) =>
                Statement ctxt

  SReturn     : forall ctxt.
                (0 term : BoolEqual ctxt.isTerminating True) =>
                (res : MaybeExpr ctxt ctxt.returns) ->
                Statement ctxt

  SPrintLn    : forall ctxt.
                {argType : GType 0} ->
                (arg : Expr ctxt argType) ->
                (cont : Statement ctxt) ->
                Statement ctxt

  SVar1       : forall ctxt.
                {newType : GType 0} ->
                (initial : Expr ctxt newType) ->
                (cont    : Statement (onDeclare1 ctxt Var $ GN newType)) ->
                Statement ctxt

  SCall       : forall ctxt.
                {retType : MaybeType} ->
                (async : Bool) ->
                (call : Call ctxt retType) ->
                (cont : Statement ctxt) ->
                Statement ctxt

  -- SChanOp     : forall ctxt.
  --               (op : ChanOp ctxt) ->
  --               (cont : Statement (onChanOp ctxt op)) ->
  --               Statement ctxt


  -- @WHEN IF_STMTS
  If          : forall ctxt.
                {tt, et : Bool} ->
                (0 term : IfTerm ctxt.isTerminating tt et) =>
                (test  : Expr ctxt GBool) ->
                (then_ : Statement $ setIsTerminating tt ctxt) ->
                (else_ : Statement $ setIsTerminating et ctxt) ->
                (cont  : MaybeCont ctxt.isTerminating ctxt) ->
                Statement ctxt
-- @END IF_STMTS

export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt