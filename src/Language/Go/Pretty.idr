module Language.Go.Pretty

import Data.Fin
import Data.List

import Language.Go.Model
import Language.Go.Aux

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy


%unbound_implicits off
%default total


public export
interface CustomChanOp where
  constructor MkCustomChanOp

  imports : {auto opts : LayoutOpts} -> Doc opts
  topLevelDecls : {auto opts : LayoutOpts} -> Doc opts

  chanOpenPP : {auto opts : LayoutOpts} ->
               (chanName : Doc opts) ->
               (elemType : Scalar) ->
               (cap : Doc opts) ->
               (Gen0 $ Doc opts)

  chanSendPP : {auto opts : LayoutOpts} ->
               (elemType : Scalar) ->
               (chanName : Doc opts) ->
               (tempName : Doc opts) ->
               (value : Doc opts) ->
               (Gen0 $ Doc opts)

  chanRecvPP : {auto opts : LayoutOpts} ->
               (elemType : Scalar) ->
               (chanName : Doc opts) ->
               (resName : Doc opts) ->
               (okName : Doc opts) ->
               (Gen0 $ Doc opts)


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

  goStr : Doc opts -> Doc opts
  goStr doc = "\"" <+> doc <+> "\""

  export
  scalarPP : Scalar -> Doc opts
  scalarPP GInt  = pure "int"
  scalarPP GBool = pure "bool"

  export
  typesPP : forall len. TypeVect len -> List (Doc opts)
  typesPP ts = assert_total map scalarPP (asList ts)

  returnTypesPP : MaybeType -> Doc opts
  returnTypesPP Nothing = empty
  returnTypesPP (Just type) = scalarPP type

  typePP : GType -> Doc opts
  typePP (GS s) = scalarPP s
  typePP (GFunc $ params `To` rets) =
    let params := goList (typesPP params)
        rets   := returnTypesPP rets
     in "func" <++> params <+?+> rets
  typePP (GChan t) = "chan" <++> scalarPP t


  export
  namePP : Decl -> (Gen0 $ Doc opts)
  namePP decl = do
    let pre := case decl.kind of
                 Var   => "v"
                 Const => "c"
                 Func  => "f"
    pure $ line $ pre <+> show decl.name

  export
  nameTypePP : Decl -> (Gen0 $ Doc opts)
  nameTypePP decl = pure $ !(namePP decl) <++> typePP decl.type


  export
  getDeclPP : (ctxt : Context) -> (idx : Fin ctxt.stackLen) -> (Gen0 $ Doc opts)
  getDeclPP ctxt idx = namePP (get idx ctxt.stack)


  export
  funcPP : (name : Doc opts) ->
           (params : List Decl) ->
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
  getChanPP : {ctxt : _} -> {0 elemType : _} ->
              GetChanDecl ctxt elemType ->
              (Gen0 $ Doc opts)
  getChanPP (ChanAt idx) = getDeclPP ctxt idx


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


parameters {cnt : Nat}
           {ctxt : Context}
           {auto opts : LayoutOpts}
           {auto customChanOp : CustomChanOp}

  export
  statementPP : forall term. Stmt cnt ctxt term -> (Gen0 $ Doc opts)

  export
  blockPP : forall term. Block cnt ctxt term -> (Gen0 $ Doc opts)

  export
  exprPP: forall retType. Expr cnt ctxt retType -> (Gen0 $ Doc opts)

  -- export
  -- multivaluedPP: {len : Nat} ->
  --                {types : TypeVect len} ->
  --                MultivaluedExpr ctxt types ->
  --                (Gen0 $ Doc opts)

  export
  exprListPP : forall len.
               {types : TypeVect len} ->
               ExprList cnt ctxt types ->
               Gen0 (List (Doc opts))

  export
  maybeExprPP : forall type. MaybeExpr cnt ctxt type -> (Gen0 $ Doc opts)
  maybeExprPP (Just expr) = exprPP expr
  maybeExprPP Nothing = pure empty

  prefixE : forall argTy.
            (op : Doc opts) ->
            (arg : Expr cnt ctxt argTy) ->
            (Gen0 $ Doc opts)
  prefixE op arg = do
    arg <- assert_total exprPP arg
    pure $ "(" <+> op <+> arg <+> ")"

  infixE : forall lhvType, rhvType.
           (op : Doc opts) ->
           (lhv : Expr cnt ctxt lhvType) ->
           (rhv : Expr (tick lhv) ctxt rhvType) ->
           (Gen0 $ Doc opts)

  funcE : forall len.
          {types : TypeVect len} ->
          (func : Doc opts) ->
          (args : ExprList cnt ctxt types) ->
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
           Call cnt ctxt types ->
           (Gen0 $ Doc opts)

  export
  sendRecvPP : ChanOp cnt ctxt -> (Gen0 $ Doc opts)


  export
  wrapBlock : forall term. (stmt : Block cnt ctxt term) -> (Gen0 $ Doc opts)


exprListPP exprs = assert_total $ traverse exprPP exprs


infixE op lhv rhv = do
  lhv <- assert_total exprPP lhv
  rhv <- assert_total exprPP rhv
  pure $ "(" <+> lhv <++> op <++> rhv <+> ")"


callPP (MkCall func args) = do
  name <- exprPP func
  funcE name args


-- @WHEN HOLES
-- @ exprPP {rets} Hole =
-- @   pure $ "<<" <+> hsepBy "," (typesPP rets) <+> ">>"
-- @END HOLES

exprPP
  {retType = (GFunc $ parTypes `To` retType)}
  (ELambda {parLen} body)
= do
  let newCtxt : Context
      newCtxt = lambdaCtxt cnt ctxt parTypes retType
      params  := takeTopDecl parLen newCtxt.stack
  body <- assert_total $ blockPP {ctxt = newCtxt} body
  funcPP empty params retType body

exprPP (ELiteral lit) =
  pure $ literalPP lit

-- exprPP (EUnary IntNeg arg) = prefixE "-" arg

-- exprPP (EBinary IntAdd lhv rhv) = infixE "+" lhv rhv
-- exprPP (EBinary IntGE lhv rhv) = infixE ">=" lhv rhv

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


statementPP {ctxt} (SReturn res) =
  pure $ "return" <+?+> !(maybeExprPP res)

-- statementPP (SPrintLn arg) = funcE "println" [arg]

statementPP {ctxt} (SVar1 {newType} initial) = do
  let newCtxt : Context; newCtxt = decl1Ctxt (tick initial) ctxt Var newType
  initial <- exprPP initial
  varPP initial newCtxt 1

statementPP (SCall async call) = do
  let pre = if async then "go" <+> space else empty
  pure $ pre <+> !(callPP call)

statementPP (SChanOp op) = sendRecvPP op

-- @WHEN IF_STMTS
statementPP (SIf test then_ else_) = do
  test  <- exprPP test
  then_ <- assert_total blockPP then_
  let skipElse = isEmpty else_ && !(chooseAnyOf Bool)
  if skipElse
     then pure $ vsep
       [ "if" <++> test  <++> "{"
       , indent' 4 then_
       , "}"
       ]
     else pure $ vsep
       [ "if" <++> test  <++> "{"
       , indent' 4 then_
       , "} else {"
       , indent' 4 !(assert_total blockPP else_)
       , "}"
       ]
-- @END IF_STMTS

-- statementPP {ctxt} (SLoop type elems body) = do
--   elems <- assert_total exprListPP elems
--   let rhv := "[]" <+> scalarPP type <+> goGeneralList "{" "}" "," elems
--   let newCtxt : Context; newCtxt = onDeclare1 ctxt Var (GS type)
--   let newVar := hsepBy comma !(traverse namePP $ takeTopDecl 1 newCtxt.stack)
--   pure $ vsep
--     [ "for" <++> newVar <++> "in range" <++> rhv <++> "{"
--     , indent' 4 !(assert_total blockPP body)
--     , "}"
--     ]


sendRecvPP {ctxt} op@(Open elemType cap) = do
  let chanName := line "v\{show $ openName cap}"
  cap' <- exprPP cap
  chanOpenPP chanName elemType cap'

sendRecvPP {ctxt} (Send {elemType} chan value) = do
  chanName <- getChanPP chan
  let tempName := tick value
      tempName' := line "v\{show tempName}"
  value' <- exprPP value
  chanSendPP elemType chanName tempName' value'

sendRecvPP {cnt} {ctxt} (Recv {elemType} chan) = do
  chanName <- getChanPP chan
  let resName  := recvName1 {cnt}
      resName' := line "v\{show resName}"
      okName  := S resName
      okName' := line "v\{show okName}"
  chanRecvPP elemType chanName resName' okName'


blockPP {ctxt} End = pure empty
blockPP {ctxt} (Term last) = statementPP last
blockPP {ctxt} (Seq head tail) =
  pure $ !(statementPP head) `vappend` !(blockPP tail)


wrapBlock {ctxt} block = do
  let rets   := returnTypesPP ctxt.returns
      params := goList !(traverse nameTypePP $
                  takeTopDecl (finToNat ctxt.blockDepth) ctxt.stack)
  block <- blockPP block
  pure $ vsep [ "package main"
              , ""
              , "func testFunc" <+> params <+?+> rets <++> "{"
              , indent' 4 block
              , "}"
              , ""
              , "func main() {"
              , "}"
              ]


export
builtinChanOp : (weightVerbose, weightSilent : Nat) -> CustomChanOp
builtinChanOp weightVerbose weightSilent = MkCustomChanOp
  { imports = imports'
  , topLevelDecls = topLevelDecls'
  , chanOpenPP = chanOpenPP'
  , chanSendPP = chanSendPP' weightVerbose weightSilent
  , chanRecvPP = chanRecvPP' weightVerbose weightSilent
  }
  where
    imports' : {auto opts : LayoutOpts} -> Doc opts
    imports' = empty

    topLevelDecls' : {auto opts : LayoutOpts} -> Doc opts
    topLevelDecls' = empty

    chanOpenPP' : {auto opts : LayoutOpts} ->
                  (chanName : Doc opts) ->
                  (elemType : Scalar) ->
                  (cap : Doc opts) ->
                  (Gen0 $ Doc opts)
    chanOpenPP' chanName elemType cap = do
      let init := goCall "make" [typePP (GChan elemType), cap]
      pure $ vsep
        [ "var" <++> chanName <++> "=" <++> init
        , "_" <++> "=" <++> chanName
        ]

    flipCoin : (wTrue, wFalse : Nat) -> Gen0 Bool
    flipCoin 0 0 = assert_total flipCoin 1 1
    flipCoin 0 (S _) = pure False
    flipCoin (S _) 0 = pure True
    flipCoin wTrue@(S _) wFalse@(S _) =
      frequency [ (FromNat wTrue, pure True), (FromNat wFalse, pure False) ]

    chanSendPP' : (verbose, silent : Nat) ->
                  {auto opts : LayoutOpts} ->
                  (elemType : Scalar) ->
                  (chanName : Doc opts) ->
                  (tempName : Doc opts) ->
                  (value : Doc opts) ->
                  (Gen0 $ Doc opts)
    chanSendPP' verbose silent elemType chanName tempName value = do
      verbOk <- flipCoin verbose silent
      verbFail <- flipCoin verbose silent
      let (tempName', tempDecl) := ifThenElse (verbOk || verbFail)
           (tempName, ["var" <++> tempName <++> "=" <++> value])
           (value, [])
      let printOk := ifThenElse verbOk
           [ indent' 4 $
               goCall "println" [goStr $ "TO" <++> chanName, tempName'] ]
           []
      let printFail := ifThenElse verbFail
           [ indent' 4 $
               goCall "println" [goStr $ "TO" <++> chanName <++> "FAILED"] ]
           []
      pure $ vsep $ join
        [ tempDecl
        , [ "select {"
          , "case" <++> chanName <++> "<-" <++> tempName' <+> ":"
          ]
        , printOk
        , [ "default:" ]
        , printFail
        , [ "}" ]
        ]


    chanRecvPP' : (verbose, silent : Nat) ->
                  {auto opts : LayoutOpts} ->
                  (elemType : Scalar) ->
                  (chanName : Doc opts) ->
                  (resName : Doc opts) ->
                  (okName : Doc opts) ->
                  (Gen0 $ Doc opts)
    chanRecvPP' verbose silent elemType chanName resName okName = do
      verbOk <- flipCoin verbose silent
      verbFail <- flipCoin verbose silent
      let printOk := ifThenElse verbOk
           [ indent' 4 $
               goCall "println" [goStr $ "FROM" <++> chanName <++> resName, resName] ]
           []
      let printFail := ifThenElse verbFail
           [ indent' 4 $
               goCall "println" [goStr $ "FROM" <++> chanName <++> resName <++> "FAILED"] ]
           []
      pure $ vsep $ join
        [ [ "var" <++> resName <++> scalarPP elemType
          , "var" <++> okName <++> "bool"
          , "select {"
          , "case" <++> resName <+> "," <++> okName <++> "= <-" <++> chanName <+> ":"
          , indent' 4 $ "_, _ =" <++> resName <+> "," <++> okName
          ]
        , printOk
        , [ "default:" ]
        , printFail
        , [ "}" ]
        ]
