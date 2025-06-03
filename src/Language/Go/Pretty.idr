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
  typeName : GoType -> Doc opts

  export
  typesPP : forall len. TypeVect len -> List (Doc opts)
  typesPP ts = assert_total map typeName (asList ts)

  returnTypesPP : forall len. TypeVect len -> Doc opts
  returnTypesPP [] = empty
  returnTypesPP [type] = typeName type
  returnTypesPP types = goGeneralList "(" ")" "," (typesPP types)

  typeName GoInt  = pure "int"
  typeName GoBool = pure "bool"
  typeName (GoFunc $ params `To` rets) =
    let params := goList (typesPP params)
        rets   := returnTypesPP rets
     in "func" <++> params <+?+> rets
-- @WHEN ASSIGNABLE_ANY
-- @   typeName GoAny = pure "interface {}"
-- @END ASSIGNABLE_ANY
  typeName (GoChan t) = "chan" <++> typeName t


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
  nameTypePP decl = pure $ !(namePP decl) <++> typeName decl.type


  export
  funcPP : forall retLen.
           (name    : Doc opts) ->
           (params  : List ResolvedDecl) ->
           (retTypes : TypeVect retLen) ->
           (body    : Doc opts) ->
           (Gen0 $ Doc opts)
  funcPP name params retTypes body =
    let params   := goList !(traverse nameTypePP params)
        retTypes := returnTypesPP retTypes
     in pure $ vsep [ "func" <++> params <+?+> retTypes <++> "{"
                    , indent' 4 body
                    , "}"
                    ]


  export
  literalPP : forall t. Literal t -> Doc opts
  literalPP (MkInt x) = line $ show x
  literalPP (MkBool True)  = "true"
  literalPP (MkBool False) = "false"

  export
  prefixName : forall par, ret. PrefixOp par ret -> Doc opts
  prefixName ChanRecv = "<-"
-- @WHEN EXTRA_BUILTINS
-- @   prefixName BoolNot  = "!"
-- @   prefixName IntNeg   = "-"
-- @END EXTRA_BUILTINS

  -- export
  -- infixPP : forall lhv, rhv, res. InfixOp lhv rhv res -> Doc opts
  -- infixPP IntAdd  = "+"
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



parameters {ctxt      : Context}
           {auto opts : LayoutOpts}

  export
  statementPP : Statement ctxt -> (Gen0 $ Doc opts)

  export
  exprPP: {retType : GoType} -> Expr ctxt retType -> (Gen0 $ Doc opts)

  -- export
  -- multivaluedPP: {len : Nat} ->
  --                {types : TypeVect len} ->
  --                MultivaluedExpr ctxt types ->
  --                (Gen0 $ Doc opts)

  export
  exprListPP : {len   : Nat} ->
               {types : TypeVect len} ->
               ExprList ctxt types ->
               Gen0 (List (Doc opts))
  exprListPP exprs =
    assert_total traverse (\(_ ** e) => exprPP e) (asList exprs)

  export
  builtinPP : {parLen : Nat} ->
              {0 retLen : Nat} ->
              {parTypes : TypeVect parLen} ->
              {retTypes : TypeVect retLen} ->
              (func : BuiltinFunc parTypes retTypes) ->
              (args : ExprList ctxt parTypes) ->
              (Gen0 $ Doc opts)
  builtinPP func args = do
      args <- exprListPP args
      let ta := typeName <$> typeArg func
      pure $ goCall (name func) (ta ++ args)
    where
      typeArg : forall parTypes, retLen.
                {retTypes : TypeVect retLen} ->
                BuiltinFunc parTypes retTypes ->
                List GoType
      typeArg {retTypes = [GoChan t]} MakeChanUnbuf = [GoChan t]
      typeArg {retTypes = [GoChan t]} MakeChanBuf = [GoChan t]
      typeArg _ = []

      name : forall parTypes, retTypes.
             BuiltinFunc parTypes retTypes ->
             Doc opts
      name PrintLn = "println"
      -- @WHEN EXTRA_BUILTINS
      -- @   name Max   = "max"
      -- @   name Min   = "min"
      -- @END EXTRA_BUILTINS
      name MakeChanUnbuf = "make"
      name MakeChanBuf   = "make"
      name ChanLen = "len"
      name ChanCap = "cap"

  -- export
  -- argsPP : {len : Nat} ->
  --          {types : TypeVect len} ->
  --          Args ctxt types ->
  --          (Gen0 $ List (Doc opts))
  -- argsPP (Comma args) = exprListPP args
  -- argsPP (Many expr) = pure [ !(multivaluedPP expr) ]

  export
  callPP : {len : Nat} ->
           {types : TypeVect len} ->
           Call ctxt types ->
           (Gen0 $ Doc opts)
  callPP (MkCall func args) = do
    name <- exprPP func
    args <- exprListPP args
    pure $ goCall name args

  export
  maybeContPP : forall isTerm. MaybeCont isTerm ctxt -> (Gen0 $ Doc opts)
  maybeContPP (Just cont) = statementPP cont
  maybeContPP Nothing     = pure empty

  export
  wrapStatement : (stmt : Statement ctxt) -> (Gen0 $ Doc opts)


-- @WHEN HOLES
-- @ exprPP {rets} Hole =
-- @   pure $ "<<" <+> hsepBy "," (typesPP rets) <+> ">>"
-- @END HOLES

exprPP
  {retType = (GoFunc $ parTypes `To` retTypes)}
  (AnonFunc {parLen} body)
= do
  let newCtxt : Context
      newCtxt = onAnonFunc ctxt parTypes retTypes
      params  := takeTopDecl parLen newCtxt.stack
  body        <- assert_total $ statementPP {ctxt = newCtxt} body
  funcPP empty params retTypes body

exprPP (GetLiteral lit) =
  pure $ literalPP lit

-- exprPP (ApplyInfix op lhv rhv) = do
--     pure $ "(" <+> !(exprPP lhv) <++> infixPP op <++> !(exprPP rhv) <+> ")"

exprPP (EPrefix op arg) = do
  pure $ "(" <+> prefixName op <+> !(exprPP arg) <+> ")"

exprPP (EBuiltin func args) = builtinPP func args

exprPP (ECall call) = callPP call

exprPP {ctxt} (GetDecl idx) = do
  let decl = resolve idx ctxt.stack
  namePP decl


-- multivaluedPP (Call func args) = do
--   name <- exprPP func
--   args <- exprListPP args
--   pure $ goCall name args


statementPP JustStop = do
  pure empty

statementPP {ctxt} (Return res) =
  -- TODO: when returns = [] we can ommit explicit return
  -- TODO: wtf?
  -- case (ctxt.returnsLen, res) of
  --   (Z, NoValue) => pure "return"
  --   (S _, Value x) => pure $ "return" <++> !(exprPP x)
  pure $ "return" <+?+> hsepBy "," !(exprListPP res)

-- statementPP {ctxt} (Void value cont) = do
--   pure $ vsep [ !(multivaluedPP value)
--               , assert_total !(statementPP cont)
--               ]

statementPP (SBuiltin func args cont) = pure $ vsep
  [ !(builtinPP func args)
  , !(assert_total $ statementPP cont)
  ]

statementPP {ctxt} (SVar1 {newType} initial cont) = do
  let count := 1
  let newCtxt : Context; newCtxt = onDeclare ctxt Var [newType]
  let newVars := hsepBy comma
                   !(traverse namePP $ takeTopDecl count newCtxt.stack)
  initial     <- exprPP initial
  let holes   := hsepBy comma $ replicate count "_"
  cont        <- assert_total $ statementPP {ctxt = newCtxt} cont
  pure $ vsep [ "var" <++> newVars <++> "=" <++> initial
              , holes <++> "=" <++> newVars
              , cont
              ]

statementPP (SCall call cont) = pure $ vsep
  [ !(callPP call)
  , !(assert_total $ statementPP cont)
  ]

-- @WHEN IF_STMTS
-- @ statementPP (If test then_ else_ cont) = do
-- @   test  <- exprPP test
-- @   then_ <- assert_total statementPP then_
-- @   cont  <- maybeContPP cont
-- @   let skipElse = isEmpty else_ && !(chooseAnyOf Bool)
-- @   if skipElse
-- @      then pure $ vsep
-- @        [ "if" <++> test  <++> "{"
-- @        , indent' 4 then_
-- @        , "}"
-- @        , cont
-- @        ]
-- @      else pure $ vsep
-- @        [ "if" <++> test  <++> "{"
-- @        , indent' 4 then_
-- @        , "} else {"
-- @        , indent' 4 !(assert_total statementPP else_)
-- @        , "}"
-- @        , cont
-- @        ]
-- @END IF_STMTS

-- statementPP (ChanSend chan value cont) =
--   pure $ vsep
--     [ !(exprPP chan) <++> "<-" <++> !(exprPP value)
--     , !(statementPP cont)
--     ]

-- statementPP {ctxt} (ChanSpecVar {type} initial cont) = do
--   let newCtxt : Context; newCtxt = onDeclare ctxt Var [type, GoBool]
--   let newVars := hsepBy comma
--                    !(traverse namePP $ takeTopDecl 2 newCtxt.stack)
--   initial     <- exprPP initial
--   let holes   := hsepBy comma $ replicate 2 "_"
--   cont        <- assert_total $ statementPP {ctxt = newCtxt} cont
--   pure $ vsep [ "var" <++> newVars <++> "=" <++> initial
--               , holes <++> "=" <++> newVars
--               , cont
--               ]

-- statementPP (Go func args cont) = do
--   func <- exprPP func
--   args <- maybeNoValuePP args
--   pure $ vsep
--     [ "go" <++> goCall func args
--     , !(statementPP cont)
--     ]


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
