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
  outerCnt : Nat
  outerCtxt : Context
  outerEStack : GValueStack outerCtxt.stack
  body : Block (lambdaCnt outerCnt paramTypes)
               (lambdaCtxt outerCnt outerCtxt paramTypes retType)
               True


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
       (0 name : Nat) ->
       (values : GValueVect types) ->
       (estack : GValueStack stack) ->
       GValueStack (push kind name types stack)
push _ _ [] stack = rewrite plusZeroRightNeutral len in stack
push kind name {count = S count'} (v :: vs) estack =
  rewrite sym $ plusSuccRightSucc len count' in
    push kind (S name) vs $ estack :< v

lambdaCtxt : (0 cnt : Nat) ->
             (0 ctxt : Context) ->
             {parLen : Nat} ->
             (0 parTypes : TypeVect parLen) ->
             (0 retType : MaybeType) ->
             (values : GValueVect parTypes) ->
             (estack : GValueStack ctxt.stack) ->
             GValueStack (lambdaCtxt cnt ctxt parTypes retType).stack
lambdaCtxt _ (MkContext {}) _ _ values estack =
  push Var _ values estack

push1 : forall len.
        (0 kind : _) ->
        (0 name : Nat) ->
        {0 newType : GType} ->
        (value : GValue newType) ->
        {0 stack : Stack len} ->
        (estack : GValueStack stack) ->
        GValueStack (push1 kind name newType stack)
push1 _ _ newValue estack = estack :< newValue

decl1Ctxt : (0 cnt : Nat) ->
             (0 ctxt : Context) ->
             (0 kind : Kind) ->
             (0 newType : GType) ->
             (newValue : GValue newType) ->
             (estack : GValueStack ctxt.stack) ->
             GValueStack (decl1Ctxt cnt ctxt kind newType).stack
decl1Ctxt _ (MkContext {}) kind _ newValue estack =
  push1 kind _ newValue estack


public export
Eval : Type -> Type
Eval type = Writer (List String) type

tellStr : String -> Eval ()
tellStr s = tell [s]


export
eval : {cnt : _} -> {ctxt : _} -> {isTerm : _} ->
       (block : Block cnt ctxt isTerm) ->
       String


parameters {cnt : Nat}
           {ctxt : Context}
           (estack : GValueStack ctxt.stack)

  evalExpr : {type : _} -> Expr cnt ctxt type -> Eval (GValue type)

  evalChanOp : (op : ChanOp cnt ctxt) ->
               Eval (GValueStack (chanOpCtxt op).stack)

  evalStmt : {isTerm : _} ->
             (stmt : Stmt cnt ctxt isTerm) ->
             Eval ( GValueStack (stmtCtxt stmt).stack
                  , GBlockValue ctxt.returns isTerm)

  evalBlock : {isTerm : _} ->
              Block cnt ctxt isTerm ->
              Eval (GBlockValue ctxt.returns isTerm)

  evalVect : forall len.
             {types : TypeVect len} ->
             ExprList cnt ctxt types ->
             Eval (GValueVect types)

  evalCall : {retType : _} ->
             Call cnt ctxt retType ->
             Eval (GMaybeValue retType)


evalChanOp {ctxt = ctxt@(MkContext {})} estack (Open _ cap) = do
  let newName : Nat; newName = openName cap
  tellStr "CREATE CHAN \{show newName}"
  pure $ decl1Ctxt newName ctxt _ _ VChan estack

evalChanOp {ctxt} estack (Send chan value) = do
  value <- evalExpr estack value
  let name := (get chan.idx ctxt.stack).name
  tellStr "SEND_TO \{show name} \{show value}"
  pure estack

evalChanOp {ctxt = ctxt@(MkContext {})} estack (Recv {elemType} chan) = do
  let name := (get chan.idx ctxt.stack).name
  let 0 ctxt1 : Context; ctxt1 = decl1Ctxt cnt ctxt Var (GS elemType)
      0 ctxt2 : Context; ctxt2 = decl1Ctxt _ ctxt1 Var (GS GBool)
      valName, okName : Nat
      valName = recvName1 cnt
      okName = S valName
      est1 : GValueStack ctxt1.stack
      est1 = decl1Ctxt valName ctxt _ _ (VUnknown "V\{show valName}") estack
      est2 : GValueStack ctxt2.stack
      est2 = decl1Ctxt okName ctxt1 _ _ (VUnknown "V\{show okName}") est1
  tellStr "RECV_FROM \{show name} V\{show valName} V\{show okName}"
  pure est2


evalStmt {ctxt = MkContext {returns = Nothing, _}} estack (SReturn Nothing) =
  pure (estack, Ret Nothing)
evalStmt {ctxt = MkContext {returns = Just _, _}} estack (SReturn $ Just expr) =
  pure (estack, Ret $ Just !(evalExpr estack expr))

evalStmt estack (SChanOp op) = pure (!(evalChanOp estack op), NoRet)

evalStmt {ctxt} estack stmt@(SVar1 initial) = do
  initial <- evalExpr estack initial
  let newCtxt : Context
      newCtxt = stmtCtxt stmt
  let newEStack : GValueStack newCtxt.stack
      newEStack = decl1Ctxt _ _ _ _ initial estack
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
      newCtxt = stmtCtxt head
  (newEStack, NoRet) <- evalStmt estack head
      | (_, Ret value) => pure $ Ret value
  rewrite stmtCtxtReturns head
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
call {paramTypes} {retType} func args = do
  let MkFuncValue { outerCnt, outerCtxt, outerEStack, body } := func
  let MkContext {} := outerCtxt
  let newCtxt : Context
      newCtxt = lambdaCtxt outerCnt outerCtxt paramTypes retType
  let estack := lambdaCtxt outerCnt outerCtxt paramTypes retType args outerEStack
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
    { outerCnt = cnt
    , outerCtxt = ctxt
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
