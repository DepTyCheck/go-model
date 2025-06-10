module Language.Go.Eval

import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Either

import Data.DPair
import Data.String
import Data.Vect

import Language.Go.Model
import Language.Go.Aux


%unbound_implicits off
%default total


public export
data GValue : GType -> Type


public export
data GValueVect : forall len. TypeVect len -> Type where
  Nil : GValueVect []
  (::) : forall t, ts.
         (head : GValue (GS t)) ->
         (tail : GValueVect ts) ->
         GValueVect (t :: ts)


public export
data GValueStack : forall len. Stack len -> Type where
  Lin : GValueStack [<]
  (:<) : forall st, t.
         (rest : GValueStack st) ->
         (top : GValue t.type) ->
         GValueStack (st :< t)


public export
record GFuncValue {parLen : _} (paramTypes : TypeVect parLen) (retType : MaybeType) where
  constructor MkFuncValue
  outerCtxt : Context
  outerEStack : GValueStack outerCtxt.stack
  body : Block (onAnonFunc outerCtxt paramTypes retType) True


data GValue : GType -> Type where
  VUnknown : forall t. (reason : String) -> GValue t

  VInt : Nat -> GValue (GS GInt)
  VBool : Bool -> GValue (GS GBool)
  VFunc : forall par, ret. GFuncValue par ret -> GValue (GFunc $ par `To` ret)
  VChan : forall elemType. GValue (GChan elemType)


public export
data GMaybeValue : MaybeType -> Type where
  Nothing : GMaybeValue Nothing
  Just : forall t. GValue (GS t) -> GMaybeValue (Just t)


public export
data GBlockValue : (returns : MaybeType) -> (isTerm : Bool) -> Type where
  Ret : forall returns, isTerm.
        (res : GMaybeValue returns) ->
        GBlockValue returns isTerm

  NoRet : forall returns. GBlockValue returns False

export
weaken : forall type, isTerm. GBlockValue type isTerm -> GBlockValue type False
weaken (Ret res) = Ret res
weaken NoRet = NoRet


export
{0 type : _} -> Show (GValue type) where
  show (VUnknown reason) = "UNKNOWN \{reason}"
  show (VInt k) = show k
  show (VBool x) = show x
  show (VFunc x) = "FUNC"
  show VChan = "CHAN"


index : forall len, type.
        (idx : Fin len) ->
        {0 stack : Stack len} ->
        (estack : GValueStack stack) ->
        (0 bt : ByType type stack idx) ->
        GValue type
index FZ (_ :< top) HereT = top
index (FS idx) (rest :< _) (ThereT there) = index idx rest there


push : forall len, count.
       (0 kind : _) ->
       {0 types : TypeVect count} ->
       {0 stack : Stack len} ->
       (values : GValueVect types) ->
       (estack : GValueStack stack) ->
       GValueStack (push kind types stack)
push _ [] stack = rewrite plusZeroRightNeutral len in stack
push kind {count = S count'} (v :: vs) estack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind vs $ estack :< v

onAnonFunc : (0 ctxt : Context) ->
             {parLen : Nat} ->
             (0 parTypes : TypeVect parLen) ->
             (0 retType : MaybeType) ->
             (values : GValueVect parTypes) ->
             (estack : GValueStack ctxt.stack) ->
             GValueStack (onAnonFunc ctxt parTypes retType).stack
onAnonFunc (MkContext {}) _ _ values estack = push Var values estack

push1 : forall len.
        (0 kind : _) ->
        {0 newType : GType} ->
        {0 stack : Stack len} ->
        (value : GValue newType) ->
        (estack : GValueStack stack) ->
        GValueStack (push1 kind newType stack)
push1 _ newValue estack = estack :< newValue

onDeclare1 : (0 ctxt    : Context) ->
             (0 kind    : Kind) ->
             (0 newType : GType) ->
             (newValue : GValue newType) ->
             (estack : GValueStack ctxt.stack) ->
             GValueStack (onDeclare1 ctxt kind newType).stack
onDeclare1 (MkContext {}) kind _ newValue estack = push1 kind newValue estack


public export
Eval : Type -> Type
Eval type = Writer (List String) type

tellStr : String -> Eval ()
tellStr s = tell [s]


export
eval : {ctxt : Context} ->
       {isTerm : Bool} ->
       (block : Block ctxt isTerm) ->
       String


parameters {ctxt : Context}
           (estack : GValueStack ctxt.stack)

  evalExpr : {type : _} -> Expr ctxt type -> Eval (GValue type)

  evalChanOp : (op : ChanOp ctxt) ->
               Eval (GValueStack (onChanOp op).stack)

  evalStmt : {isTerm : _} ->
             (stmt : Stmt ctxt isTerm) ->
             Eval ( GValueStack (onStmt stmt).stack
                  , GBlockValue ctxt.returns isTerm)

  evalBlock : {isTerm : _} ->
              Block ctxt isTerm ->
              Eval (GBlockValue ctxt.returns isTerm)

  evalVect : forall len.
             {types : TypeVect len} ->
             ExprList ctxt types ->
             Eval (GValueVect types)

  evalCall : {retType : _} -> Call ctxt retType -> Eval (GMaybeValue retType)


evalChanOp {ctxt = ctxt@(MkContext {})} estack (Open cap) = do
  tellStr "CREATE CHAN \{show ctxt.stackLen}"
  pure $ onDeclare1 ctxt _ _ VChan estack

evalChanOp {ctxt = MkContext {}} estack (Send chan value) = do
  value <- evalExpr estack value
  tellStr "SEND_TO \{show chan.idx} \{show value}"
  pure estack

evalChanOp {ctxt = ctxt@(MkContext {})} estack (Recv {elemType} chan) = do
  tellStr "RECV_FROM \{show chan.idx}"
  let 0 ctxt1 : Context; ctxt1 = onDeclare1 ctxt Var (GS elemType)
      0 ctxt2 : Context; ctxt2 = onDeclare1 ctxt1 Var (GS GBool)
      est1 : GValueStack ctxt1.stack
      est1 = onDeclare1 ctxt _ _ (VUnknown "FROM CHAN \{show chan.idx}") estack
      est2 : GValueStack ctxt2.stack
      est2 = onDeclare1 ctxt1 _ _ (VUnknown "IS_FULL \{show chan.idx}") est1
  pure est2


evalStmt {ctxt = MkContext {returns = Nothing, _}} estack (SReturn Nothing) =
  pure (estack, Ret Nothing)
evalStmt {ctxt = MkContext {returns = Just _, _}} estack (SReturn $ Just expr) =
  pure (estack, Ret $ Just !(evalExpr estack expr))

evalStmt estack (SChanOp op) = pure (!(evalChanOp estack op), NoRet)

evalStmt {ctxt} estack stmt@(SVar1 initial) = do
  initial <- evalExpr estack initial
  let newCtxt : Context
      newCtxt = onStmt stmt
  let newEStack : GValueStack newCtxt.stack
      newEStack = onDeclare1 _ _ _ initial estack
  pure (newEStack, NoRet)

evalStmt estack (SCall async call) = do
  when async $ tellStr "GO"
  _ <- evalCall estack call
  when async $ tellStr "ENDGO"
  pure (estack, NoRet)

evalStmt {ctxt} {isTerm} estack (SIf {branch} test then_ else_) = do
  test <- evalExpr estack test
  case test of
    VBool True => do
      res <- evalBlock estack then_
      pure (estack, goThen branch res)
    VBool False => do
      res <- evalBlock estack else_
      pure (estack, goElse branch res)
    VUnknown reason => do
      tellStr "IF \{reason}"
      _ <- evalBlock estack then_
      tellStr "ELSE"
      _ <- evalBlock estack else_
      tellStr "ENDIF"
      pure (estack, goUnknown ctxt.returns isTerm)

  where
    goThen : forall type, term, tt, te.
             IfTerm term tt te ->
             GBlockValue type tt ->
             GBlockValue type term
    goThen TTT val = val
    goThen FFT val = val
    goThen FTF val = weaken val

    goElse : forall type, term, tt, te.
             IfTerm term tt te ->
             GBlockValue type te ->
             GBlockValue type term
    goElse TTT val = val
    goElse FFT val = weaken val
    goElse FTF val = val

    goUnknown : (type : _) -> (term : _) -> GBlockValue type term
    goUnknown type False = NoRet
    goUnknown (Just x) True = Ret $ Just $ VUnknown "UNKNOWN_IF_RESULT"
    goUnknown Nothing True = Ret Nothing


evalBlock estack End = pure NoRet
evalBlock estack (Term last) = do
  (_, result) <- evalStmt estack last
  pure result

evalBlock {ctxt} {isTerm} estack (Seq head tail) = do
  let newCtxt : Context
      newCtxt = onStmt head
  (newEStack, NoRet) <- evalStmt estack head
      | (_, Ret value) => pure $ Ret value
  rewrite onStmtReturns head
  evalBlock {ctxt = newCtxt} newEStack tail


evalVect estack [] = pure []
evalVect estack (e :: es) =
  pure $ !(assert_total evalExpr estack e) :: !(evalVect estack es)


export
call : {parLen : _} ->
       {paramTypes : TypeVect parLen} ->
       {retType : _} ->
       (func : GFuncValue paramTypes retType) ->
       (args : GValueVect paramTypes) ->
       Eval (GMaybeValue retType)
call {paramTypes} {retType} (MkFuncValue { outerCtxt, outerEStack, body }) args = do
  let MkContext {} := outerCtxt
  let newCtxt : Context
      newCtxt = onAnonFunc outerCtxt paramTypes retType
  let estack := onAnonFunc outerCtxt paramTypes retType args outerEStack
  Ret res <- assert_total evalBlock estack body
  pure res


evalCall estack (MkCall func args) = do
  (VFunc f) <- assert_total evalExpr estack func
  | (VUnknown _) => do
    tellStr "UNKNOWN_CALL"
    pure $ case retType of
      Nothing => Nothing
      Just _ => Just $ VUnknown "UNKNOWN_CALL_RESULT"
  args <- evalVect estack args
  call f args


evalExpr estack (ELambda body) =
  pure $ VFunc $ MkFuncValue
    { outerCtxt = ctxt
    , outerEStack = estack
    , body = body
    }

evalExpr _ (ELiteral (MkInt k)) = pure $ VInt k
evalExpr _ (ELiteral (MkBool x)) = pure $ VBool x

evalExpr estack (ECall call) = do
  (Just res) <- evalCall estack  call
  pure res

evalExpr estack (EGetDecl idx {bt}) = pure $ index idx estack bt


eval {ctxt} {isTerm} block =
  unlines $ execWriter $ evalBlock (unknowns ctxt.stack) block

  where
    unknowns : (stack : _) -> GValueStack stack
    unknowns [<] = [<]
    unknowns (x :< y) = unknowns x :< VUnknown "GIVEN"
