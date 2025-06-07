module Language.Go.Pretty

import Data.Fin
import Data.List

import Language.Go.Model
import Language.Go.Aux

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy


%unbound_implicits off
%default total

export
indentWidth : Nat
indentWidth = 4

parameters {auto opts : LayoutOpts}
  hsepBy : (delim : Doc opts) -> List (Doc opts) -> Doc opts
  hsepBy _ [] = empty
  hsepBy delim (head :: tail) =
    foldl (\lhv, rhv => lhv <+> delim <++> rhv) head tail

  vsepBy : (delim : Doc opts) -> List (Doc opts) -> Doc opts
  vsepBy _ [] = empty
  vsepBy delim (head :: tail) =
    foldl (\lhv, rhv => (lhv <+> delim) `vappend` rhv) head tail

  sepBy : (delim : Doc opts) -> List (Doc opts) -> Doc opts
  sepBy delim docs =
    ifMultiline (hsepBy delim docs) (vsepBy delim docs)


  goGeneralList : (left, right, sep : Doc opts) ->
                  (content : List (Doc opts)) ->
                  Doc opts
  goGeneralList left right delim content =
    (left <+> hsepBy delim content <+> right)

  goList : (content : List (Doc opts)) -> Doc opts
  goList = goGeneralList "(" ")" ","

  goEnclose : (left, right, content : Doc opts) -> Doc opts
  goEnclose left right content =
    goGeneralList left right empty [content]

  goCall : (func : Doc opts) -> (args : List $ Doc opts) -> Doc opts
  goCall func args = func <+> goList args


  export
  typePP : forall ord. GType ord -> Doc opts

  export
  typesPP : forall len. TypeVect len -> List (Doc opts)
  typesPP ts = assert_total map typePP (asList ts)

  returnTypesPP : MaybeType -> Doc opts
  returnTypesPP Nothing = empty
  returnTypesPP (Just type) = typePP type

  typePP GInt  = pure "int"
  typePP GBool = pure "bool"
  typePP (GFunc $ params `To` rets) =
    let params := goList (typesPP params)
        rets   := returnTypesPP rets
     in "func" <++> params <+?+> rets
  typePP (GChan t) = "chan" <++> typePP t


  export
  namePP : ResolvedDecl -> (Gen0 $ Doc opts)
  namePP decl = do
    let pre := case decl.kind of
                 Var   => "v"
                 Const => "c"
                 Func  => "f"
    pure $ line $ pre <+> show decl.name

  export
  nameTypePP : ResolvedDecl -> (Gen0 $ Doc opts)
  nameTypePP decl = pure $ !(namePP decl) <++> typePP (snd decl.type)


  export
  getDeclPP : (ctxt : Context) -> (idx : Fin ctxt.stackLen) -> (Gen0 $ Doc opts)
  getDeclPP ctxt idx = namePP (resolve idx ctxt.stack)


  export
  funcPP : (name : Doc opts) ->
           (params : List ResolvedDecl) ->
           (retType : MaybeType) ->
           (body : Doc opts) ->
           (Gen0 $ Doc opts)
  funcPP name params retType body =
    let params := goList !(traverse nameTypePP params)
        retType := returnTypesPP retType
     in pure $ vsep [ "func" <++> params <+?+> retType <++> "{"
                    , indent' 4 body
                    , "}"
                    ]


  export
  literalPP : forall t. Literal t -> Doc opts
  literalPP (MkInt x) = line $ show x
  literalPP (MkBool True)  = "true"
  literalPP (MkBool False) = "false"

  export
  varPP : (initial : Doc opts) ->
          (newCtxt : Context) ->
          (count : Nat) ->
          (Gen0 $ Doc opts)
  varPP initial newCtxt count = do
    let newVars := hsepBy comma
                     !(traverse namePP $ takeTopDecl count newCtxt.stack)
    let holes := hsepBy comma $ replicate count "_"
    pure $ vsep [ "var" <++> newVars <++> "=" <++> initial
                , holes <++> "=" <++> newVars
                ]


parameters {ctxt      : Context}
           {auto opts : LayoutOpts}

  export
  statementPP : Statement ctxt -> (Gen0 $ Doc opts)

  export
  exprPP: forall retType. Expr ctxt retType -> (Gen0 $ Doc opts)

  -- export
  -- multivaluedPP: {len : Nat} ->
  --                {types : TypeVect len} ->
  --                MultivaluedExpr ctxt types ->
  --                (Gen0 $ Doc opts)

  export
  exprListPP : forall len.
               {types : TypeVect len} ->
               ExprList ctxt types ->
               Gen0 (List (Doc opts))
  exprListPP exprs =
    assert_total traverse (\(_ ** e) => exprPP e) (asList exprs)

  export
  maybeExprPP : forall type. MaybeExpr ctxt type -> (Gen0 $ Doc opts)
  maybeExprPP (Just expr) = exprPP expr
  maybeExprPP Nothing = pure empty

  export
  getChanPP : forall elemType. GetChanDecl ctxt elemType -> (Gen0 $ Doc opts)
  getChanPP (ChanAt idx) = getDeclPP ctxt idx

  prefixE : forall argTy.
            (op : Doc opts) ->
            (arg : Expr ctxt argTy) ->
            (Gen0 $ Doc opts)
  prefixE op arg = do
    arg <- assert_total exprPP arg
    pure $ "(" <+> op <+> arg <+> ")"

  infixE : forall lhvType, rhvType.
           (op : Doc opts) ->
           (lhv : Expr ctxt lhvType) ->
           (rhv : Expr ctxt rhvType) ->
           (Gen0 $ Doc opts)
  infixE op lhv rhv = do
    lhv <- assert_total exprPP lhv
    rhv <- assert_total exprPP rhv
    pure $ "(" <+> lhv <++> op <++> rhv <+> ")"

  funcE : forall len.
          {types : TypeVect len} ->
          (func : Doc opts) ->
          (args : ExprList ctxt types) ->
          (Gen0 $ Doc opts)
  funcE func args = pure $ goCall func !(exprListPP args)


  -- export
  -- argsPP : {len : Nat} ->
  --          {types : TypeVect len} ->
  --          Args ctxt types ->
  --          (Gen0 $ List (Doc opts))
  -- argsPP (Comma args) = exprListPP args
  -- argsPP (Many expr) = pure [ !(multivaluedPP expr) ]

  export
  callPP : forall types.
           Call ctxt types ->
           (Gen0 $ Doc opts)
  callPP (MkCall func args) = do
    name <- exprPP func
    funcE name args

  export
  maybeContPP : forall isTerm. MaybeCont isTerm ctxt -> (Gen0 $ Doc opts)
  maybeContPP (Just cont) = statementPP cont
  maybeContPP Nothing     = pure empty

  export
  sendRecvPP : ChanOp ctxt -> (Gen0 $ Doc opts)


  export
  wrapStatement : (stmt : Statement ctxt) -> (Gen0 $ Doc opts)

-- @WHEN HOLES
-- @ exprPP {rets} Hole =
-- @   pure $ "<<" <+> hsepBy "," (typesPP rets) <+> ">>"
-- @END HOLES

exprPP
  {retType = (GFunc $ parTypes `To` retType)}
  (ELambda {parLen} body)
= do
  let newCtxt : Context
      newCtxt = onAnonFunc ctxt parTypes retType
      params  := takeTopDecl parLen newCtxt.stack
  body <- assert_total $ statementPP {ctxt = newCtxt} body
  funcPP empty params retType body

exprPP (ELiteral lit) =
  pure $ literalPP lit

exprPP (EUnary IntNeg arg) = prefixE "-" arg

exprPP (EBinary IntAdd lhv rhv) = infixE "+" lhv rhv
exprPP (EBinary IntGE lhv rhv) = infixE ">=" lhv rhv

  -- builtinPP (ChanLen chan) = do
  --   pure $ goCall "len" [!(getChanPP chan)]
-- @WHEN EXTRA_BUILTINS
-- @   prefixName BoolNot  = "!"
-- @   prefixName IntNeg   = "-"
-- @END EXTRA_BUILTINS

-- @WHEN EXTRA_BUILTINS
-- @   infixPP IntSub  = "-"
-- @   infixPP IntMul  = "*"
-- @   infixPP BoolAnd = "&&"
-- @   infixPP BoolOr  = "||"
-- @   infixPP IntEq   = "=="
-- @   infixPP IntNE   = "!="
-- @   infixPP IntLt   = "<"
-- @   infixPP IntLE   = "<="
-- @   infixPP IntGt   = ">"
-- @   infixPP IntGE   = ">="
-- @END EXTRA_BUILTINS

exprPP (ECall call) = callPP call

exprPP {ctxt} (EGetDecl idx) = getDeclPP ctxt idx


-- multivaluedPP (Call func args) = do
--   name <- exprPP func
--   args <- exprListPP args
--   pure $ goCall name args


statementPP SStop = pure empty

statementPP {ctxt} (SReturn res) =
  pure $ "return" <+?+> !(maybeExprPP res)

statementPP (SPrintLn arg cont) = pure $ vsep
  [ !(funcE "println" [arg])
  , !(assert_total $ statementPP cont)
  ]

statementPP {ctxt} (SVar1 {newType} initial cont) = do
  let newCtxt : Context; newCtxt = onDeclare1 ctxt Var (GN newType)
  initial <- exprPP initial
  pure $ vsep [ !(varPP initial newCtxt 1)
              , !(assert_total $ statementPP {ctxt = newCtxt} cont)
              ]

statementPP (SCall async call cont) = do
  let pre = if async then "go" <+> space else empty
  pure $ vsep
    [ pre <+> !(callPP call)
    , !(assert_total $ statementPP cont)
    ]

-- statementPP (SChanOp op cont) = pure $ vsep
--     [ !(sendRecvPP op)
--     , !(assert_total $ statementPP cont)
--     ]

-- @WHEN IF_STMTS
statementPP (If test then_ else_ cont) = do
  test  <- exprPP test
  then_ <- assert_total statementPP then_
  cont  <- maybeContPP cont
  let skipElse = isEmpty else_ && !(chooseAnyOf Bool)
  if skipElse
     then pure $ vsep
       [ "if" <++> test  <++> "{"
       , indent' 4 then_
       , "}"
       , cont
       ]
     else pure $ vsep
       [ "if" <++> test  <++> "{"
       , indent' 4 then_
       , "} else {"
       , indent' 4 !(assert_total statementPP else_)
       , "}"
       , cont
       ]
-- @END IF_STMTS

-- statementPP (ChanSend chan value cont) =
--   pure $ vsep
--     [ !(exprPP chan) <++> "<-" <++> !(exprPP value)
--     , !(statementPP cont)
--     ]

-- statementPP {ctxt} (ChanSpecVar {type} initial cont) = do
--   let newCtxt : Context; newCtxt = onDeclare ctxt Var [type, GBool]
--   let newVars := hsepBy comma
--                    !(traverse namePP $ takeTopDecl 2 newCtxt.stack)
--   initial     <- exprPP initial
--   let holes   := hsepBy comma $ replicate 2 "_"
--   cont        <- assert_total $ statementPP {ctxt = newCtxt} cont
--   pure $ vsep [ "var" <++> newVars <++> "=" <++> initial
--               , holes <++> "=" <++> newVars
--               , cont
--               ]


sendRecvPP {ctxt} op@(Open {elemType} cap) = do
  cap <- exprPP cap
  varPP ("<-" <++> goCall "make" [typePP (GChan elemType), cap]) (onChanOp ctxt op) 1

sendRecvPP {ctxt} (Send chan value) =
  pure $ !(getChanPP chan) <++> "<-" <++> !(exprPP value)

sendRecvPP {ctxt} op@(Recv varCount chan) = do
  let initial := "<-" <++> !(getChanPP chan)
  varPP initial (onChanOp ctxt op) (finToNat varCount)


wrapStatement {ctxt} stmt = do
  let rets   := returnTypesPP ctxt.returns
      params := goList !(traverse nameTypePP $
                  takeTopDecl (finToNat ctxt.blockDepth) ctxt.stack)
  stmt <- statementPP stmt
  pure $ vsep [ "package main"
              , ""
              , "func testFunc" <+> params <+?+> rets <++> "{"
              , indent' 4 stmt
              , "}"
              , ""
              , "func main() {"
              , "}"
              ]
