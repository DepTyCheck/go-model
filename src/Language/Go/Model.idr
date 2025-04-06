module Language.Go.Model

import Data.Fuel
import Data.Nat
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Properties
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE

import Generics.Derive

import Test.DepTyCheck.Gen

%language ElabReflection
%unbound_implicits off

%hide Language.Reflection.TTImp.Decl

namespace GoType
  mutual
    ||| Types from Go Language
    |||
    ||| GoInt <-> int
    ||| GoAny <-> interface {}
    ||| Note: GoAny can slow down generation if there are any non constructible types
    public export
    data GoType : Type where
      GoInt, GoBool : GoType
      GoFunc : GoFuncType -> GoType
      -- @WHEN ASSIGNABLE_ANY
      -- @ | GoAny
      -- @END ASSIGNABLE_ANY

    public export
    data GoFuncType : Type where
      MkGoFuncType : {n_par, n_ret : Nat} ->
                     (par : TypeVect n_par) ->
                     (ret : TypeVect n_ret) ->
                     GoFuncType

    public export
    data TypeVect : (len : Nat) -> Type where
      Nil : TypeVect 0
      (::) : forall len. GoType -> TypeVect len -> TypeVect (S len)

  public export
  asVect : forall len. TypeVect len -> Vect len GoType
  asVect [] = []
  asVect (t :: ts) = t :: asVect ts

  export
  Biinjective GoType.(::) where
    biinjective Refl = (Refl, Refl)

  -- TODO: looks ugly
  {n_par, n_ret : Nat} -> Biinjective (MkGoFuncType {n_par} {n_ret}) where
    biinjective Refl = (Refl, Refl)

  injective' : forall np1, nr1, np2, nr2.
               {p1 : TypeVect np1} ->
               {r1 : TypeVect nr1} ->
               {p2 : TypeVect np2} ->
               {r2 : TypeVect nr2} ->
               (MkGoFuncType {n_par = np1} {n_ret = nr1} p1 r1 =
                MkGoFuncType {n_par = np2} {n_ret = nr2} p2 r2) ->
               (np1 = np2, nr1 = nr2)
  injective' Refl = (Refl, Refl)

  mutual
    %runElab derive "GoType" [Generic, DecEq]

    export
    DecEq GoFuncType where
      decEq (MkGoFuncType {n_par = np1} {n_ret = nr1} p1 r1)
            (MkGoFuncType {n_par = np2} {n_ret = nr2} p2 r2) =
        case (decEq np1 np2, decEq nr1 nr2) of
             (Yes Refl, Yes Refl) =>
                decEqCong2 {f = MkGoFuncType {n_par = np1} {n_ret = nr1}}
                           (decEq p1 p2) (decEq r1 r2)
             (No contra, Yes _) => No $ \eq =>
                                  contra $ fst $ injective' eq
             (_, No contra) => No $ \eq =>
                              contra $ snd $ injective' eq


    export
    {len : Nat} -> DecEq (TypeVect len) where
      decEq Nil Nil = Yes Refl
      decEq (xs :: x) (xs' :: x') =
        assert_total decEqCong2 (decEq xs xs') (decEq x x')


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
  -- @END ASSIGNABLE_ANY


namespace Decl
  public export
  data Kind
    = Var
    | Const
    | Func

  public export
  data Name : (n : Nat) -> Type where
    Shadows : forall n. Fin n -> Name n
    UniqueName : forall n. Name n

  public export
  weakenLTE : forall m, n. Name n -> LTE n m -> Name m
  weakenLTE UniqueName lte = UniqueName
  weakenLTE (Shadows fm) lte = Shadows (weakenLTE fm lte)

  public export
  record Decl (index : Nat) where
    constructor MkDecl
    kind : Kind
    type : GoType
    shadows : Name index


namespace Stack
  public export
  data Stack : (len : Nat) -> Type where
    Lin : Stack Z
    (:<) : forall len. Stack len -> Decl len -> Stack (S len)


  ||| Proof that `decl` doesn't shadows other daclaration at `idx`
  public export
  data NotShadow : forall len. (decl : Decl len) -> (idx : Fin len) -> Type where
    ShadowNothing : forall idx, kind, type.
                    NotShadow (MkDecl kind type UniqueName) idx

    ShadowOther : forall len, kind, type.
                  {0 shadowed, idx : Fin len} ->
                  (0 so : So $ shadowed /= idx) =>
                  NotShadow (MkDecl kind type (Shadows shadowed)) idx


  public export
  data ByType : forall len. GoType -> Stack len -> Fin len -> Type where
    HereT : forall ty, kind, shadows, tail.
            ByType ty (tail :< (MkDecl kind ty shadows)) FZ

    ThereT : forall ty, head, tail, found.
             ByType ty tail found ->
             (ns : NotShadow head found) =>
             ByType ty (tail :< head) (weaken found)


  -- public export
  -- data ByRet : forall len. (ret : GoTypes) -> Stack len ->
  --              RelativeTo len -> (params : GoTypes) -> Type where
  --   HereR : forall par, ret, kind, shadows, tail.
  --           ByRet ret
  --                 (tail :< (kind ** MkDecl (GoFunc par ret) shadows))
  --                 (Rel _ FZ)
  --                 par

  --   ThereR : forall par, ret, head, tail, depth.
  --            ByRet ret tail depth par ->
  --            (ns : NotShadow head depth) =>
  --            ByRet ret (tail :< head) (incHeight depth) par



--   public export
--   fromList : 

-- namespace NewShadows
--   public export
--   data NewShadows : (start, count, limit : Nat) -> Type where
--     Nil : forall start, limit. NewShadows start 0 limit
--     (::) : forall start, count, limit.
--            Name limit ->
--            NewShadows (S start) count limit ->
--            NewShadows start (S count) limit

-- public export
-- push : forall len, limit.
--        (kind : Kind) ->
--        (types : GoTypes) ->
--        (lte : LTE limit len) =>
--        NewShadows len (length types) limit ->
--        Stack len ->
--        Stack (len + length types)
-- push _ [] [] bs =
--   rewrite plusZeroRightNeutral len in bs
-- push {len} kind (t :: ts) @{lte} (s :: ss) stack =
--   rewrite sym $ plusSuccRightSucc len (length ts) in
--     let lte' : (LTE limit (S len)) = lteSuccRight lte in
--       push kind ts ss (stack :< MkDecl kind t (weakenLTE s lte))


namespace Context
  public export
  record Context where
    constructor MkContext
    stackLen : Nat
    stack : Stack stackLen
    blockStart : Fin (S stackLen)
    returnsLen : Nat
    returns : TypeVect returnsLen
    isTerminating : Bool

  public export
  SetIsTerminating : Bool -> Context -> Context
  SetIsTerminating value = { isTerminating := value }

  public export
  PushDecl : (ctxt : Context) ->
             Decl ctxt.stackLen ->
             Context
  PushDecl ctxt decl =
    { stackLen $= S
    , stack $= flip (:<) decl
    , blockStart $= weaken
    } ctxt


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
  data  BuiltinFunc : {n_par, n_ret : Nat} ->
                      (paramTypes : TypeVect n_par) ->
                      (retTypes : TypeVect n_ret) ->
                      Type where
    -- @WHEN ASSIGNABLE_ANY
    -- @ Print : BuiltinFunc [GoAny] []
    -- @UNLESS ASSIGNABLE_ANY
    Print : BuiltinFunc [GoInt] []
    -- @END ASSIGNABLE_ANY

    -- @WHEN EXTRA_BUILTINS
    -- @ Max, Min : BuiltinFunc [GoInt, GoInt] [GoInt]
    -- @END EXTRA_BUILTINS

  -- public export
  -- OnAnonFunc : (oldCtxt : Context) ->
  --              {paramsCount : Nat} ->
  --              (params : NewDecls Var oldCtxt.stackLen paramsCount) ->
  --              (retTypes : GoTypes) ->
  --              Context
  -- OnAnonFunc oldCtxt params retTypes =
  --   let newStack = push params oldCtxt.stack in
  --   { isTerminating := True
  --   , returns := retTypes
  --   , stackLen := _
  --   , stack := newStack
  --   } oldCtxt

  -- TODO: {len : Nat} VS {0 len : Nat} in data decls

  mutual
    public export
    data ExprList : (ctxt : Context) ->
                    {len : Nat} ->
                    (rets : TypeVect len) ->
                    Type where
      Nil : forall ctxt. ExprList ctxt []
      (::) : forall ctxt, headTy, tailTypes.
             (head : Expr ctxt [headTy]) ->
             (tail : ExprList ctxt tailTypes) ->
             ExprList ctxt (headTy :: tailTypes)

    public export
    data Expr : (ctxt : Context) ->
                {len : Nat} ->
                (res : TypeVect len) ->
                Type where
      -- AnonFunc : forall ctxt.
      --            {paramsCount : Nat} ->
      --            (params : NewDecls Var ctxt.stackLen paramsCount) ->
      --            (retTypes : GoTypes) ->
      --            (body : Statement (OnAnonFunc ctxt params retTypes)) ->
      --            Expr ctxt [GoFunc (types params) retTypes]

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
                    (args : Expr ctxt argTypes) ->
                    Expr ctxt retTypes

      -- CallNamed : forall ctxt, retTypes.
      --             (idx : RelativeTo ctxt.stackLen) ->
      --             {argTypes : GoTypes} ->
      --             (br : ByRet retTypes ctxt.stack idx argTypes) =>
      --             (args : ExprList ctxt argTypes) ->
      --             Expr ctxt retTypes

      GetDecl : forall ctxt, ty.
                (idx : Fin ctxt.stackLen) ->
                (bt : ByType ty ctxt.stack idx) =>
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
  data BoolEqual : Bool -> Bool -> Type where
    Refl : forall b. BoolEqual b b

  public export
  data AllowJustStop : Context -> Type where
    StopUnlessShouldReturn : AllowJustStop (MkContext { isTerminating = False, _ })
    StopWhenReturnNone : AllowJustStop (MkContext { returns = [], _ })

  public export
  data AllowReturnValue : Context -> Type where
    MkAllowReturnValue : forall ret, stackLen, blockStart, returnsLen.
                         {0 rets : TypeVect returnsLen} ->
                         {0 stack : Stack stackLen} ->
                         AllowReturnValue (MkContext
                                          { isTerminating = True
                                          , returnsLen = S returnsLen
                                          , returns = (ret :: rets)
                                          , stack = stack
                                          , stackLen = stackLen
                                          , blockStart = blockStart
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

  -- public export
  -- OnDeclare : (ctxt : Context) ->
  --             (kind : Kind) ->
  --             (newTypes : GoTypes) ->
  --             (newShadows : NewShadows ctxt.stackLen
  --                                      (length newTypes)
  --                                      (finToNat ctxt.blockStart)) ->
  --             Context
  -- OnDeclare ctxt kind newTypes newShadows =
  --   let lte' : (LTE (S (finToNat ctxt.blockStart)) (S ctxt.stackLen)) :=
  --     elemSmallerThanBound ctxt.blockStart
  --     ; LTESucc lte = lte'
  --     ; cbLteNewLen : (LTE (S ctxt.stackLen) (S (ctxt.stackLen + length newTypes)))
  --     ; cbLteNewLen = LTESucc (lteAddRight ctxt.stackLen)
  --   in
  --     { stackLen := ctxt.stackLen + length newTypes
  --     , stack := push kind newTypes @{lte} newShadows ctxt.stack
  --     , blockStart := weakenLTE ctxt.blockStart cbLteNewLen
  --     } ctxt

  -- public export
  -- record DeclareStmt (ctxt : Context) (kind : Kind) where
  --   constructor MkDeclareStmt
  --   newTypes : GoTypes
  --   newShadows : NewShadows ctxt.stackLen (length newTypes) (finToNat ctxt.blockStart)
  --   initial : Expr ctxt newTypes
  --   cont : Statement $ OnDeclare ctxt kind newTypes newShadows

  -- public export
  -- record DeclareStmt (ctxt : Context) (kind : Kind) where
  --   constructor MkDeclareStmt
  --   newType : GoType
  --   newName : Name (finToNat ctxt.blockStart)
  --   initial : Expr ctxt [newType]
  --   cont : Statement (PushDecl ctxt (MkDecl newName newType))


  data Statement : (ctxt : Context) -> Type where
    -- DeclareVar : forall ctxt.
    --              (decl : DeclareStmt ctxt Var) ->
    --              Statement ctxt

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
genExprs : Fuel -> (ctxt : Context) -> {len : Nat} -> (rets : TypeVect len) ->
                   Gen MaybeEmpty $ Expr ctxt rets
