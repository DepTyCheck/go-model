module Language.Go.Pretty

import Data.List

import Language.Go.Model
import Language.Go.Aux

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy


%unbound_implicits off
%default total


--------------------------------------------------------------------------------
--                               Interface
--------------------------------------------------------------------------------

parameters {auto opts : LayoutOpts}

  export
  typePP   : GoType -> Doc opts

  export
  typesPP  : TypeVectL -> List (Doc opts)

  export
  namePP   : ResolvedDecl -> (Gen0 $ Doc opts)

  export
  literalPP  : forall t. Literal t -> Doc opts

  export
  infixPP    : forall lhv, rhv, res. InfixOp lhv rhv res -> Doc opts

  export
  builtinPP  : forall par, ret. BuiltinFunc par ret -> Doc opts

  export
  paramListPP    : List (Doc opts) -> Doc opts

  export
  retTypesListPP : List (Doc opts) -> Doc opts

  export
  callPP  : (func, args : Doc opts) -> Doc opts

  export
  byComma : Doc opts -> Doc opts -> Doc opts


parameters {ctxt      : Context}
           {auto opts : LayoutOpts}

  export
  exprPP : {0 rets : TypeVectL} -> Expr ctxt rets -> (Gen0 $ Doc opts)

  export
  statementPP : Statement ctxt -> (Gen0 $ Doc opts)

  export
  wrapStatement : (stmt : Statement ctxt) -> (Gen0 $ Doc opts)


  -- @WHEN IF_STMTS
-- @   export
-- @   printIf : {ctxtTest, ctxtThen, ctxtElse : Context} ->
-- @             (test : Expr ctxtTest [GoBool]) ->
-- @             (thenBranch : Statement ctxtThen) ->
-- @             (elseBranch : Statement ctxtElse) ->
-- @             Printer
  -- @END IF_STMTS

--------------------------------------------------------------------------------
--                            Implementations
--------------------------------------------------------------------------------


typePP GoInt  = pure "int"
typePP GoBool = pure "bool"
typePP (GoFunc params rets) =
  let params := paramListPP (typesPP params)
      rets   := retTypesListPP (typesPP rets)
   in "func" <++> params <++> rets
-- @WHEN ASSIGNABLE_ANY
-- @ printType GoAny = pure "interface {}"
-- @END ASSIGNABLE_ANY


typesPP ts = assert_total map typePP (asList ts)


namePP decl = do
  let pre := case decl.kind of
               Var   => "v"
               Const => "c"
               Func  => "f"
  pure $ line $ pre <+> show decl.name


literalPP (MkInt x) = line $ show x
literalPP (MkBool True) = "true"
literalPP (MkBool False) = "false"


-- @WHEN EXTRA_BUILTINS
-- @ Show (PrefixOp _ _) where
-- @   show BoolNot = "!"
-- @   show IntNeg = "-"
-- @END EXTRA_BUILTINS


infixPP IntAdd = "+"
-- @WHEN EXTRA_BUILTINS
-- @ infixPP IntSub = "-"
-- @ infixPP IntMul = "*"
-- @ infixPP BoolAnd = "&&"
-- @ infixPP BoolOr = "||"
-- @ infixPP IntEq = "=="
-- @ infixPP IntNE = "!="
-- @ infixPP IntLt = "<"
-- @ infixPP IntLE = "<="
-- @ infixPP IntGt = ">"
-- @ infixPP IntGE = ">="
-- @END EXTRA_BUILTINS


builtinPP Print = "print"
-- @WHEN EXTRA_BUILTINS
-- @ builtinPP Max = "max"
-- @ builtinPP Min = "min"
-- @END EXTRA_BUILTINS


paramListPP docs =
  "(" <+> (foldl byComma empty docs) <+> ")"


retTypesListPP [] = empty
retTypesListPP docs = paramListPP docs


callPP func args =
  func <+> "(" <+> args <+> ")"


byComma lhv rhv = lhv <+> comma <++> rhv


-- @WHEN HOLES
exprPP (Hole type) =
  pure $ "<<" <++> foldl byComma empty (typesPP type) <++> ">>"
-- @END HOLES

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
  pure $ callPP (builtinPP f) !(exprPP args)

-- exprPP {ctxt} (AnonFunc paramTypes retTypes body) = do
--   -- TODO: make more convenient interface
--   let decls = map (Declare Var) $ asList paramTypes
--   let params' = enumerate {start = ctxt.stackDepth} decls
--   params <- printDeclList {typed = True} params'
--   body <- assert_total printStatement body
--   rets <- printNoneOneOrList printType (asList retTypes)
--   pure $ vsep [ "func" <++> "(" <+> params <+> ")" <++> rets <++> "{"
--               , indent' 4 body
--               , "}"
--               ]

-- exprPP (CallNamed idx args) = do
--   args <- exprPPList args
--   let decl = index idx ctxt.stack
--   fn <- printName idx decl
--   pure $ funcCall fn args

exprPP {ctxt} (GetDecl idx) = do
  let decl = resolve idx ctxt.stack
  namePP decl

-- exprPP (Comma a b rest) = exprPPList (a :: b :: rest)


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

statementPP
  {ctxt}
  (DeclareVar newTypes newNames initial cont)
= do
  let count   := 1
  let newCtxt : Context; newCtxt = OnDeclare ctxt Var newTypes newNames
  let newVars := foldr byComma empty
                   !(traverse namePP $ takeTopDecl count newCtxt)
  initial     <- exprPP initial
  let holes   := foldr byComma empty $ List.Lazy.replicate count "_"
  cont        <- assert_total $ statementPP {ctxt = newCtxt} cont
  pure $ vsep [ "var" <++> "_" <++> "=" <++> initial
              , cont
              ]
  -- pure $ vsep [ "var" <++> newVars <++> "=" <++> initial
  --             , "_" <++> "=" <++> newVars
  --             , cont
  --             ]

statementPP JustStop = do
  pure ""

statementPP (ReturnValue res) = do
  pure $ "return" <++> !(exprPP res)

statementPP ReturnNone = do
  pure "return"

statementPP (VoidExpr expr cont) = do
  pure $ !(exprPP expr) `vappend` !(statementPP cont)

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


-- wrapStatement {ctxt} stmt = do
--   let ret := retTypesListPP (typesPP ctxt.returns)
--   let params = takeFrom 0 ctxt.stack
--   args <- "<args>" -- TODO printDeclList {typed = True} params
--   stmt <- statementPP stmt
--   pure $ vsep [ "package main"
--               , ""
--               , "func testFunc(" <+> args <+> ")" <++> ret <++> "{"
--               , indent' 4 stmt
--               , "}"
--               , ""
--               , "func main() {"
--               , "}"
--               ]


-- wrapExpr {ctxt} expr = do
--   let params = enumerate $ asList ctxt.stack
--   args <- printDeclList {typed = True} params
--   expr <- exprPP expr
--   let store = "temp :=" <++> expr
--   pure $ vsep [ "package main"
--               , ""
--               , "func testFunc(" <+> args <+> ")" <++> "{"
--               , indent' 4 store
--               , indent' 4 "print(temp)"
--               , "}"
--               , ""
--               , "func main() {"
--               , "}"
--               ]
