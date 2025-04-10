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


  goGeneralList
    :  (left, right, sep : Doc opts)
    -> (content : List (Doc opts))
    -> Doc opts
  goGeneralList left right delim content =
    ifMultiline
      (left <+> hsepBy delim content <+> right)
      (vsep [left, indent indentWidth (vsepBy delim content), right])

  goList : (content : List (Doc opts)) -> Doc opts
  goList = goGeneralList "(" ")" ","

  goEnclose : (left, right, content : Doc opts) -> Doc opts
  goEnclose left right content =
    goGeneralList left right empty [content]


  export
  typePP : GoType -> Doc opts

  export
  typesPP : forall len. TypeVect len -> List (Doc opts)
  typesPP ts = assert_total map typePP (asList ts)

  returnTypesPP : forall len. TypeVect len -> Doc opts
  returnTypesPP [] = empty
  returnTypesPP [type] = typePP type
  returnTypesPP types = goGeneralList "(" ")" "," (typesPP types)

  typePP GoInt  = pure "int"
  typePP GoBool = pure "bool"
  typePP (GoFunc $ params `To` rets) =
    let params := goList (typesPP params)
        rets   := returnTypesPP rets
     in "func" <++> params <+?+> rets
-- @WHEN ASSIGNABLE_ANY
-- @   typePP GoAny = pure "interface {}"
-- @END ASSIGNABLE_ANY


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
  nameTypePP decl = pure $ !(namePP decl) <++> typePP decl.type


  export
  funcPP:
       forall retLen
    .  (name    : Doc opts)
    -> (params  : List ResolvedDecl)
    -> (returns : TypeVect retLen)
    -> (body    : Doc opts)
    -> (Gen0 $ Doc opts)
  funcPP name params returns body =
    let params  := goList !(traverse nameTypePP params)
        returns := returnTypesPP returns
     in pure $ vsep [ "func" <++> params <+?+> returns <++> "{"
                    , indent' 4 body
                    , "}"
                    ]


  export
  literalPP : forall t. Literal t -> Doc opts
  literalPP (MkInt x) = line $ show x
  literalPP (MkBool True) = "true"
  literalPP (MkBool False) = "false"

  export
  infixPP : forall lhv, rhv, res. InfixOp lhv rhv res -> Doc opts
  infixPP IntAdd = "+"
-- @WHEN EXTRA_BUILTINS
-- @   infixPP IntSub = "-"
-- @   infixPP IntMul = "*"
-- @   infixPP BoolAnd = "&&"
-- @   infixPP BoolOr = "||"
-- @   infixPP IntEq = "=="
-- @   infixPP IntNE = "!="
-- @   infixPP IntLt = "<"
-- @   infixPP IntLE = "<="
-- @   infixPP IntGt = ">"
-- @   infixPP IntGE = ">="
-- @END EXTRA_BUILTINS

  export
  builtinPP : forall par, ret. BuiltinFunc par ret -> Doc opts
  builtinPP Print = "print"
-- @WHEN EXTRA_BUILTINS
-- @   builtinPP Max = "max"
-- @   builtinPP Min = "min"
-- @END EXTRA_BUILTINS

  export
  callPP  : (func : Doc opts) -> (args : List $ Doc opts) -> Doc opts
  callPP func args = func <+> goList args


parameters {ctxt      : Context}
           {auto opts : LayoutOpts}

  export
  statementPP : Statement ctxt -> (Gen0 $ Doc opts)

  export
  exprPP:
       {len  : Nat}
    -> {rets : TypeVect len}
    -> Expr ctxt rets
    -> (Gen0 $ Doc opts)

  export
  exprListPP:
       {len   : Nat}
    -> {types : TypeVect len}
    -> ExprList ctxt types
    -> Gen0 (List (Doc opts))
  exprListPP exprs =
    assert_total traverse (\(_ ** e) => exprPP e) (asList exprs)

  export
  commaPP:
       {len    : Nat}
    -> {aT, bT : GoType}
    -> {restT  : TypeVect len}
    -> (a      : Expr ctxt [aT])
    -> (b      : Expr ctxt [bT])
    -> (rest   : ExprList ctxt restT)
    -> (Gen0 (List (Doc opts)))
  commaPP a b rest = exprListPP $ a :: b :: rest

  export
  maybeNoValuePP:
       {len   : Nat}
    -> {types : TypeVect len}
    -> MaybeNoValue ctxt types
    -> (Gen0 (List (Doc opts)))
  maybeNoValuePP (NoValue) = pure [empty]
  maybeNoValuePP (Value (Comma a b rest)) = commaPP a b rest
  maybeNoValuePP (Value expr) = pure [ !(exprPP expr) ]

  export
  wrapStatement : (stmt : Statement ctxt) -> (Gen0 $ Doc opts)


-- @WHEN HOLES
-- @ exprPP {rets} Hole =
-- @   pure $ "<<" <+> hsepBy "," (typesPP rets) <+> ">>"
-- @END HOLES

exprPP (Comma a b rest) =
  pure $ "/* Comma! */" <++> hsepBy "," !(commaPP a b rest)

exprPP
  {rets = [GoFunc $ parTypes `To` retTypes]}
  (AnonFunc {parCount} parNames body)
= do
  let newCtxt : Context
      newCtxt = OnAnonFunc ctxt parTypes parNames retTypes
      params  := takeTopDecl parCount newCtxt.stack
  body        <- assert_total $ statementPP {ctxt = newCtxt} body
  funcPP empty params retTypes body

exprPP (GetLiteral lit) =
  pure $ literalPP lit

-- @WHEN EXTRA_BUILTINS
-- @ exprPP (ApplyPrefix op arg) = do
-- @   arg <- exprPP arg
-- @   pure $ "(" <+> line (show op) <+> arg <+> ")"
-- @END EXTRA_BUILTINS

exprPP (ApplyInfix op lhv rhv) = do
    pure $ "(" <+> !(exprPP lhv) <++> infixPP op <++> !(exprPP rhv) <+> ")"

exprPP (CallBuiltin f args) = do
  args <- exprListPP args
  pure $ callPP (builtinPP f) args

exprPP (CallNamed idx args) = do
  name <- namePP (resolve idx ctxt.stack)
  args <- maybeNoValuePP args
  pure $ callPP name args

exprPP {ctxt} (GetDecl idx) = do
  let decl = resolve idx ctxt.stack
  namePP decl


-- @WHEN IF_STMTS
-- @   export
-- @   printIf : {ctxtTest, ctxtThen, ctxtElse : Context} ->
-- @             (test : Expr ctxtTest [GoBool]) ->
-- @             (thenBranch : Statement ctxtThen) ->
-- @             (elseBranch : Statement ctxtElse) ->
-- @             Printer
-- @END IF_STMTS


-- @WHEN IF_STMTS
-- @ printIf test thenBranch elseBranch = do
-- @   test <- exprPP test
-- @   thenBranch <- assert_total printStatement thenBranch
-- @   let top = hangSep 0 ("if" <++> test) "{"
-- @   let skipElse = isEmpty elseBranch && !(chooseAnyOf Bool)
-- @   if skipElse
-- @      then pure $ vsep [ top
-- @                       , indent' 4 thenBranch
-- @                       , "}"
-- @                       ]
-- @      else do
-- @        elseBranch <- assert_total printStatement elseBranch
-- @        pure $ vsep [ top
-- @                    , indent' 4 thenBranch
-- @                    , "} else {"
-- @                    , indent' 4 elseBranch
-- @                    , "}"
-- @                    ]
-- @END IF_STMTS

statementPP JustStop = do
  pure empty

-- TODO: when returns = [] we can ommit explicit return
statementPP {ctxt} (Return res) =
  -- TODO: wtf?
  -- case (ctxt.returnsLen, res) of
  --   (Z, NoValue) => pure "return"
  --   (S _, Value x) => pure $ "return" <++> !(exprPP x)
  pure $ "return" <+?+> hsepBy "," !(maybeNoValuePP res)

statementPP (VoidExpr expr cont) = do
  pure $ !(exprPP expr) `vappend` !(statementPP cont)

statementPP
  {ctxt}
  (DeclareVar {count} newTypes newNames initial cont)
= do
  let newCtxt : Context; newCtxt = OnDeclare ctxt Var newTypes newNames
  let newVars := hsepBy comma
                   !(traverse namePP $ takeTopDecl count newCtxt.stack)
  initial     <- exprPP initial
  let holes   := hsepBy comma $ replicate count "_"
  cont        <- assert_total $ statementPP {ctxt = newCtxt} cont
  pure $ vsep [ "var" <++> newVars <++> "=" <++> initial
              , "_" <++> "=" <++> newVars
              , cont
              ]

-- @WHEN IF_STMTS
-- @ statementPP (InnerIf test {isTermThen} {isTermElse} th el cont) = do
-- @   ifText <- printIf test th el
-- @   contText <- statementPP cont
-- @   pure $ ifText `vappend` contText

-- @ statementPP (TermIf test th el) = do
-- @   ifText <- printIf test th el
-- @   pure ifText
-- @END IF_STMTS

-- statementPP (DeclareVar stmt) = do
--   var <- printDecl (newIndex stmt) (newDecl stmt)
--   initial <- exprPP stmt.initial
--   let decl = "var" <++> var <++> "=" <++> initial
--   let use = "_" <++> "=" <++> var
--   cont <- assert_total statementPP stmt.cont
--   pure $ vsep [ decl
--               , use
--               , cont
--               ]


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
