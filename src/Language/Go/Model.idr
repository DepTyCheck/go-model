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


namespace TypeVect
  public export
  data TypeVect : (len : Nat) -> Type


public export
record TypeVectL where
  constructor MkVectL
  {len : Nat}
  vect : TypeVect len


public export
data GoType : Type where
  GoInt  : GoType
  GoBool : GoType
  GoFunc : (params  : TypeVectL) -> (returns : TypeVectL) -> GoType
  -- @WHEN ASSIGNABLE_ANY
-- @   | GoAny
  -- @END ASSIGNABLE_ANY

namespace TypeVect
  data TypeVect : (len : Nat) -> Type where
    Nil  : TypeVect 0
    (::) : forall len. GoType -> TypeVect len -> TypeVect (S len)

export
Biinjective TypeVect.(::) where
  biinjective Refl = (Refl, Refl)

export
Biinjective GoFunc where
  biinjective Refl = (Refl, Refl)


mutual
  %runElab derive "GoType" [Generic, DecEq]

  export
  {0 len : Nat} -> DecEq (TypeVect len) where
    decEq Nil Nil = Yes Refl
    decEq (t1 :: ts1) (t2 :: ts2) =
      assert_total decEqCong2 (decEq t1 t2) (decEq ts1 ts2)

  export
  DecEq TypeVectL where
    decEq (MkVectL {len = len1} ts1) (MkVectL {len = len2} ts2) =
      let Yes Refl := decEq len1 len2
          | No contra => No $ \eq => contra $ fst $ injDP eq
          Yes eqVect := decEq ts1 ts2
          | No contra => No $ \eq => contra $ snd $ injDP eq
       in Yes $ congDP eqVect

      where
        congDP
          : {0 len1, len2 : Nat}
          -> {0 ts1 : TypeVect len1}
          -> {0 ts2 : TypeVect len2}
          -> (0 _   : (ts1 = ts2))
          -> ((MkVectL {len = len1} ts1) = (MkVectL {len = len2} ts2))
        congDP Refl = Refl

        injDP
          : {0 len1, len2 : Nat}
          -> {0 ts1 : TypeVect len1}
          -> {0 ts2 : TypeVect len2}
          -> (0 _   : (MkVectL {len = len1} ts1) = (MkVectL {len = len2} ts2))
          -> (len1 = len2, ts1 = ts2)
        injDP Refl = (Refl, Refl)


public export
data IsEmpty : TypeVectL -> Type where
  ItIsEmpty : IsEmpty (MkVectL [])


public export
data NonEmpty : TypeVectL -> Type where
  IsNotEmpty
    :  {0 len  : Nat}
    -> {0 head : GoType}
    -> {0 tail : TypeVect len}
    -> NonEmpty (MkVectL (head :: tail))


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
data Name : (height : Nat) -> Type where
  Shadows    : forall height. Fin height -> Name height
  UniqueName : forall height. Name height

public export
map : forall n, m . (Fin n -> Fin m) -> Name n -> Name m
map _ UniqueName = UniqueName
map f (Shadows n) = Shadows (f n)


public export
record Decl (height : Nat) where
  constructor MkDecl
  kind : Kind
  name : Name height
  type : GoType


namespace Stack
  public export
  data Stack : (len : Nat) -> Type where
    Lin  : Stack Z
    (:<) : forall len. Stack len -> Decl len -> Stack (S len)


||| Proof that `decl` doesn't shadows other daclaration at `idx`
public export
data NotShadow
  : forall len. (decl : Decl len) -> (idx : Fin len) -> Type
  where
    ShadowNothing
      :  forall idx, kind, type
      .  NotShadow (MkDecl kind UniqueName type) idx

    ShadowOther
      :  forall len, kind, type
      .  {0 other, idx : Fin len}
      -> {auto 0 so    : So $ other /= idx}
      -> NotShadow (MkDecl kind (Shadows other) type) idx

public export
data ByType : forall len. GoType -> Stack len -> Fin len -> Type where
  HereT
    :  forall ty, kind, name, tail
    .  ByType ty (tail :< MkDecl kind name ty) FZ

  ThereT
    :  forall ty, head, tail, found
    .  (there     : ByType ty tail found)
    -> {auto 0 ns : NotShadow head found}
    -> ByType ty (tail :< head) (FS found)


  -- public export
  -- data ByRet : forall len. (ret : GoTypes) -> Stack len ->
  --              RelativeTo len -> (params : GoTypes) -> Type where
  --   HereR : forall par, ret, kind, name, tail.
  --           ByRet ret
  --                 (tail :< (kind ** MkDecl (GoFunc par ret) name))
  --                 (Rel _ FZ)
  --                 par

  --   ThereR : forall par, ret, head, tail, depth.
  --            ByRet ret tail depth par ->
  --            (ns : NotShadow head depth) =>
  --            ByRet ret (tail :< head) (incHeight depth) par


namespace NewNames'
  public export
  data NewNames' : (count, limit : Nat) -> Type where
    Nil : forall limit. NewNames' 0 limit

    (::)
      :  forall count, limit
      .  Name limit
      -> NewNames' count limit
      -> NewNames' (S count) limit

public export
push'
  :  forall limit, count
  .  {offset : Nat}
  -> Kind
  -> TypeVect count
  -> NewNames' count limit
  -> Stack (limit + offset)
  -> Stack (limit + offset + count)
push' _ [] [] stack =
  rewrite plusZeroRightNeutral (limit + offset) in stack
push' {count = S count'} {limit} {offset}
     kind (t :: ts) (n :: ns) stack
  = let name'  := rewrite plusCommutative limit offset in map (shift offset) n
        stack' : (Stack (limit + S offset)) :=
          rewrite sym $ plusSuccRightSucc limit offset in
            stack :< MkDecl kind name' t
     in rewrite succ3_2 limit offset count' in push' kind ts ns stack'

  where
    succ3_2 : (0 a, b, c : Nat) -> (a + b + S c) = (a + S b + c)
    succ3_2 a b c =
      Calc $
        |~ a + b + S c
        ~~ S (a + b + c) ... (sym $ plusSuccRightSucc (a + b) c)
        ~~ S (a + b) + c ... (Refl)
        ~~ (a + S b + c) ... (cong (+ c) (plusSuccRightSucc a b))

public export
push
  :  {count, len : Nat}
  -> {limit      : Fin (S len)}
  -> Kind
  -> TypeVect count
  -> NewNames' count (finToNat limit)
  -> Stack len
  -> Stack (len + count)
push {count} {limit} {len} kind ts ns stack =
  let offset : Nat
      offset = finToNat (complement limit)

      limPlusOffEqLen : (finToNat limit + offset = len)
      limPlusOffEqLen := injective $ complementSpec limit

      stack' : Stack (finToNat limit + offset) :=
        rewrite limPlusOffEqLen in stack

   in rewrite sym limPlusOffEqLen in
        push' kind ts ns stack'


public export
record Context where
  constructor MkContext
  stackLen      : Nat
  stack         : Stack stackLen
  blockDepth    : Fin (S stackLen)
  returns       : TypeVectL
  isTerminating : Bool

public export
SetIsTerminating : Bool -> Context -> Context
SetIsTerminating value = { isTerminating := value }


public export
record NewNames (count : Nat) (ctxt : Context) where
  constructor MkNewNames
  newNames : NewNames' count (finToNat ctxt.blockDepth)


public export
data Statement : (ctxt : Context) -> Type


public export
data Literal : (ty : GoType) -> Type where
  MkInt  : Nat  -> Literal GoInt
  MkBool : Bool -> Literal GoBool

-- @WHEN EXTRA_BUILTINS
-- @ public export
-- @ data PrefixOp : (argTy, resTy : GoType) -> Type where
-- @   BoolNot : PrefixOp GoBool GoBool
-- @   IntNeg  : PrefixOp GoInt GoInt
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
data  BuiltinFunc : (paramTypes, retTypes : TypeVectL) -> Type where
  -- @WHEN ASSIGNABLE_ANY
-- @   Print : BuiltinFunc [GoAny] []
  -- @UNLESS ASSIGNABLE_ANY
  Print : BuiltinFunc (MkVectL [GoInt]) (MkVectL [])
  -- @END ASSIGNABLE_ANY

  -- @WHEN EXTRA_BUILTINS
-- @   Max, Min : BuiltinFunc (2 ** [GoInt, GoInt]) (1 ** [GoInt])
  -- @END EXTRA_BUILTINS


public export
data Expr : (ctxt : Context) -> (res : TypeVectL) -> Type


namespace ExprList
  public export
  data ExprList : (ctxt : Context) -> (types : TypeVectL) -> Type where
    Nil  : forall ctxt. ExprList ctxt (MkVectL [])

    (::)
      :  forall ctxt, headT, tailLen
      .  {0 tailT : TypeVect tailLen}
      -> (head    : Expr ctxt (MkVectL [headT]))
      -> (tail    : ExprList ctxt (MkVectL tailT))
      -> ExprList ctxt (MkVectL (headT :: tailT))


public export
OnAnonFunc
  :  {paramCount : Nat}
  -> (ctxt       : Context)
  -> (paramTypes : TypeVect paramCount)
  -> (paramNames : NewNames paramCount ctxt)
  -> (retTypes   : TypeVectL)
  -> Context
OnAnonFunc {paramCount} ctxt newTypes (MkNewNames newNames) retTypes =
  { stackLen      $= (+ paramCount)
  , stack         $= push Var newTypes newNames
  , blockDepth    := natToFinLT @{prf paramCount ctxt.stackLen} paramCount
  , returns       := retTypes
  , isTerminating := True
  } ctxt

  where
    0 prf : (0 a, b : Nat) -> LT a (S $ b + a)
    prf a b = rewrite plusCommutative b a in
                LTESucc $ lteAddRight {m = b} a


data Expr : (ctxt : Context) -> (res : TypeVectL) -> Type where
-- @WHEN HOLES
-- @   Hole
-- @     :  forall ctxt
-- @     .  (type       : TypeVectL)
-- @     -> Expr ctxt type
-- @END HOLES

  AnonFunc
    :  forall ctxt, retTypes
    .  {parCount   : Nat}
    -> {0 parTypes : TypeVect parCount}
    -> (parNames   : NewNames parCount ctxt)
    -> (body       : Statement (OnAnonFunc ctxt parTypes parNames retTypes))
    -> Expr ctxt (MkVectL [GoFunc (MkVectL parTypes) retTypes])

  GetLiteral
    :  forall ctxt, resTy
    .  (lit        : Literal resTy)
    -> Expr ctxt (MkVectL [resTy])

  -- @WHEN EXTRA_BUILTINS
-- @   ApplyPrefix : forall ctxt, resTy, argTy.
-- @                 (op : PrefixOp argTy resTy) ->
-- @                 (arg : Expr ctxt [argTy]) ->
-- @                 Expr ctxt [resTy]
  -- @END EXTRA_BUILTINS

  ApplyInfix
    :  forall ctxt, resTy
    .  {lhvTy      : GoType}
    -> {rhvTy      : GoType}
    -> (op         : InfixOp lhvTy rhvTy resTy)
    -> (lhv        : Expr ctxt (MkVectL [lhvTy]))
    -> (rhv        : Expr ctxt (MkVectL [rhvTy]))
    -> Expr ctxt (MkVectL [resTy])

  CallBuiltin
    :  forall ctxt, retTypes
    .  {paramTypes : TypeVectL}
    -> (func       : BuiltinFunc paramTypes retTypes)
    -> (args       : Expr ctxt paramTypes)
    -> Expr ctxt retTypes

  -- CallNamed : forall ctxt, retTypes.
  --             (idx : RelativeTo ctxt.stackLen) ->
  --             {argTypes : GoTypes} ->
  --             (br : ByRet retTypes ctxt.stack idx argTypes) =>
  --             (args : ExprList ctxt argTypes) ->
  --             Expr ctxt retTypes

  GetDecl
    :  forall ctxt, ty
    .  (idx          : Fin ctxt.stackLen)
    -> {auto 0 bt    : ByType ty ctxt.stack idx}
    -> Expr ctxt (MkVectL [ty])

  -- CallExpr : forall ctxt, argTypes, retTypes.
  --            (f : Expr ctxt [GoFunc argTypes retTypes]) ->
  --            (args : Expr ctxt argTypes) ->
  --            Expr ctxt retTypes

  Comma
    :  forall ctxt
    .  {0 count'' : Nat}
    -> {0 ret     : TypeVect (S (S count''))}
    -> (values    : ExprList ctxt (MkVectL ret))
    -> Expr ctxt (MkVectL ret)


public export
data BoolEqual : Bool -> Bool -> Type where
  Refl : forall b. BoolEqual b b


public export
data AllowJustStop : Context -> Type where
  StopNonTerminating
    :  forall ctxt
    .  {auto 0 prf : BoolEqual ctxt.isTerminating False}
    -> AllowJustStop ctxt

  StopWhenReturnsNone
    :  forall ctxt
    .  {auto 0 prf : IsEmpty ctxt.returns}
    -> AllowJustStop ctxt


-- @WHEN IF_STMTS
-- @ public export
-- @ data AllowInnerIf : (isTermThen : Bool) ->
-- @                     (isTermElse : Bool) ->
-- @                     Type where
-- @   AllowInnerIfTT : AllowInnerIf True True
-- @   AllowInnerIfTF : AllowInnerIf True False
-- @   AllowInnerIfFT : AllowInnerIf False True
-- @END IF_STMTS


public export
OnDeclare
  :  {count    : Nat}
  -> (ctxt     : Context)
  -> (kind     : Kind)
  -> (newTypes : TypeVect count)
  -> (newNames : NewNames count ctxt)
  -> Context
OnDeclare ctxt kind newTypes (MkNewNames newNames) =
  { stackLen   $= (+ count)
  , stack      $= push kind newTypes newNames
  , blockDepth := rewrite plusCommutative ctxt.stackLen count in
                    rewrite plusSuccRightSucc count ctxt.stackLen in
                      shift count ctxt.blockDepth
  } ctxt


data Statement : (ctxt : Context) -> Type where
  DeclareVar
    :  {0 ctxt      : Context}
    -- -> {count'      : Nat}
    -> (newTypes    : TypeVect 1)
    -> (newNames    : NewNames 1 ctxt)
    -> (initial     : Expr ctxt (MkVectL newTypes))
    -> (cont        : Statement (OnDeclare ctxt Var newTypes newNames))
    -> Statement ctxt

  JustStop
    :  {0 ctxt      : Context}
    -> {auto 0 a    : AllowJustStop ctxt}
    -> Statement ctxt

  ReturnValue
    :  {0 ctxt      : Context}
    -> {auto 0 ne   : NonEmpty ctxt.returns}
    -> {auto 0 term : BoolEqual ctxt.isTerminating True}
    -> (res         : Expr ctxt ctxt.returns)
    -> Statement ctxt

  ReturnNone
    :  {0 ctxt      : Context}
    -> {auto 0 em   : IsEmpty ctxt.returns}
    -> {auto 0 term : BoolEqual ctxt.isTerminating True}
    -> Statement ctxt

  VoidExpr
    :  {0 ctxt      : Context}
    -> (expr        : Expr ctxt (MkVectL []))
    -> (cont        : Statement ctxt)
    -> Statement ctxt

  -- @WHEN IF_STMTS
-- @   InnerIf : forall ctxt.
-- @             (test : Expr ctxt [GoBool]) ->
-- @             {isTermThen, isTermElse: Bool} ->
-- @             (ai : AllowInnerIf isTermThen isTermElse) =>
-- @             (th : Statement $ SetIsTerminating isTermThen ctxt) ->
-- @             (el : Statement $ SetIsTerminating isTermElse ctxt) ->
-- @             (cont : Statement ctxt) ->
-- @             Statement ctxt

-- @   TermIf : forall ctxt, ret.
-- @            IsTerminating ctxt ret =>
-- @            (test : Expr ctxt [GoBool]) ->
-- @            (th : Statement ctxt) ->
-- @            (el : Statement ctxt) ->
-- @            Statement ctxt
  -- @END IF_STMTS


export
genStatements : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

export
genExprs
  :  Fuel
  -> (ctxt : Context)
  -> (rets : TypeVectL)
  -> Gen MaybeEmpty $ Expr ctxt rets