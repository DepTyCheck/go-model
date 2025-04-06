module Language.Go.Pretty

import Data.Alternative
import Data.Fuel
import Data.List
import Data.DPair

import Language.Go.Model
import Language.Go.Aux

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen


%unbound_implicits off
%default total


public export
Printer : Type
Printer = {opts : _} -> (Gen0 $ Doc opts)

--------------------------------------------------------------------------------
--                               Interface
--------------------------------------------------------------------------------

export
printList : forall t. (t -> Printer) -> List t -> Printer

export
printNoneOneOrList : forall t. (t -> Printer) -> List t -> Printer

export
printType : GoType -> Printer

export
printTypeList : forall len. TypeVect len -> Printer

export
printName : ResolvedDecl -> Printer

export
printDecl : {default False typed : Bool} ->
            ResolvedDecl ->
            Printer

export
printDeclList : {default False typed : Bool} ->
                List ResolvedDecl ->
                Printer

export
funcCall : {opts : _} -> (f, args : Doc opts) -> Doc opts

export
printExprList : forall ts. {ctxt : Context} -> ExprList ctxt ts -> Printer

export
printExpr : {0 len  : Nat} ->
            {0 rets : TypeVect len} ->
            {ctxt   : Context} ->
            Expr ctxt rets ->
            Printer

-- @WHEN IF_STMTS
-- @ export
-- @ printIf : {ctxtTest, ctxtThen, ctxtElse : Context} ->
          -- @ (test : Expr ctxtTest [GoBool]) ->
          -- @ (thenBranch : Statement ctxtThen) ->
          -- @ (elseBranch : Statement ctxtElse) ->
          -- @ Printer
-- @END IF_STMTS

export
printStatement : {ctxt : Context} ->
                 Statement ctxt ->
                 Printer

export
wrapStatement : {ctxt : Context} ->
                (stmt : Statement ctxt) ->
                Printer

export
wrapExpr : forall rets.
           {ctxt : Context} ->
           (stmt : Expr ctxt rets) ->
           Printer

--------------------------------------------------------------------------------
--                            Implementations
--------------------------------------------------------------------------------


printList pp [] = pure $ line ""
printList pp [x] = pp x
printList pp (x :: xs) = do
  x <- pp x
  xs <- printList pp xs
  pure $ x <+> "," <++> xs


printNoneOneOrList pp [] = pure $ line ""
printNoneOneOrList pp [x] = pp x
printNoneOneOrList pp xs = do
  items <- printList pp xs
  pure $ enclose "(" ")" items


printType GoInt = pure "int"
printType GoBool = pure "bool"
printType (GoFunc $ MkGoFuncType params rets) {opts} = do
  params <- printTypeList params
  let params = enclose "(" ")" params
  rets <- printNoneOneOrList (assert_total printType) (asList rets)
  pure $ "func" <+> params <++> rets

-- @WHEN ASSIGNABLE_ANY
-- @ printType GoAny = pure "interface {}"
-- @END ASSIGNABLE_ANY


printTypeList ts = printList (assert_total printType) (asList ts)


printName decl = do
  let pre = case decl.kind of
                 Var => "v"
                 Const => "c"
                 Func => "f"
  pure $ line $ pre <+> show decl.name


printDecl {typed} decl {opts} = do
  name <- printName decl {opts}
  if typed
     then do
       ty <- printType decl.type
       pure $ name <++> ty
     else
       pure name


printDeclList {typed} =
  printList (\(_ ** decl) => printDecl {typed} decl)


funcCall f args = f <+> "(" <+> args <+> ")"


printExprList es =
  printList (\(Evidence _ x) => assert_total printExpr x) (asList es)


Show (Literal _) where
  show (MkInt x) = show x
  show (MkBool True) = "true"
  show (MkBool False) = "false"


-- @WHEN EXTRA_BUILTINS
-- @ Show (PrefixOp _ _) where
  -- @ show BoolNot = "!"
  -- @ show IntNeg = "-"
-- @END EXTRA_BUILTINS


Show (InfixOp _ _ _) where
  show IntAdd = "+"
  -- @WHEN EXTRA_BUILTINS
  -- @ show IntSub = "-"
  -- @ show IntMul = "*"
  -- @ show BoolAnd = "&&"
  -- @ show BoolOr = "||"
  -- @ show IntEq = "=="
  -- @ show IntNE = "!="
  -- @ show IntLt = "<"
  -- @ show IntLE = "<="
  -- @ show IntGt = ">"
  -- @ show IntGE = ">="
  -- @END EXTRA_BUILTINS


{n_par, n_ret : Nat}
-> {par : TypeVect n_par}
-> {ret : TypeVect n_ret}
-> Show (BuiltinFunc par ret) where
  show Print = "print"
  -- @WHEN EXTRA_BUILTINS
  -- @ show Max = "max"
  -- @ show Min = "min"
  -- @END EXTRA_BUILTINS


printExpr (GetLiteral lit) = pure $ line $ show lit

-- @WHEN EXTRA_BUILTINS
-- @ printExpr (ApplyPrefix op arg) = do
  -- @ arg <- printExpr arg
  -- @ pure $ "(" <+> line (show op) <+> arg <+> ")"
-- @END EXTRA_BUILTINS

printExpr (ApplyInfix op lhv rhv) = do
    lhv <- printExpr lhv
    rhv <- printExpr rhv
    pure $ "(" <+> lhv <++> line (show op) <++> rhv <+> ")"

printExpr (CallBuiltin f args) = do
  args <- printExpr args
  pure $ funcCall (line $ show f) args

-- printExpr {ctxt} (AnonFunc paramTypes retTypes body) = do
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

-- printExpr (CallNamed idx args) = do
--   args <- printExprList args
--   let decl = index idx ctxt.stack
--   fn <- printName idx decl
--   pure $ funcCall fn args

printExpr {ctxt} (GetDecl idx) = do
  let decl = resolve idx ctxt.stack
  printName decl

-- printExpr (Comma a b rest) = printExprList (a :: b :: rest)


-- @WHEN IF_STMTS
-- @ printIf test thenBranch elseBranch = do
  -- @ test <- printExpr test
  -- @ thenBranch <- assert_total printStatement thenBranch
  -- @ let top = hangSep 0 ("if" <++> test) "{"
  -- @ let skipElse = isEmpty elseBranch && !(chooseAnyOf Bool)
  -- @ if skipElse
     -- @ then pure $ vsep [ top
                      -- @ , indent' 4 thenBranch
                      -- @ , "}"
                      -- @ ]
     -- @ else do
       -- @ elseBranch <- assert_total printStatement elseBranch
       -- @ pure $ vsep [ top
                   -- @ , indent' 4 thenBranch
                   -- @ , "} else {"
                   -- @ , indent' 4 elseBranch
                   -- @ , "}"
                   -- @ ]
-- @END IF_STMTS


printStatement JustStop = pure ""

printStatement (ReturnValue res) = do
  resText <- printExpr res
  pure $ "return" <++> resText

printStatement ReturnNone = do
  pure $ "return"

printStatement (VoidExpr expr cont) = do
  e <- printExpr expr
  contText <- printStatement cont
  pure $ e `vappend` contText

-- @WHEN IF_STMTS
-- @ printStatement (InnerIf test {isTermThen} {isTermElse} th el cont) = do
  -- @ ifText <- printIf test th el
  -- @ contText <- printStatement cont
  -- @ pure $ ifText `vappend` contText

-- @ printStatement (TermIf test th el) = do
  -- @ ifText <- printIf test th el
  -- @ pure ifText
-- @END IF_STMTS

-- printStatement (DeclareVar stmt) = do
--   var <- printDecl (newIndex stmt) (newDecl stmt)
--   initial <- printExpr stmt.initial
--   let decl = "var" <++> var <++> "=" <++> initial
--   let use = "_" <++> "=" <++> var
--   cont <- assert_total printStatement stmt.cont
--   pure $ vsep [ decl
--               , use
--               , cont
--               ]


wrapStatement {ctxt} stmt = do
  ret <- printTypeList ctxt.returns
  let params = enumerate $ asList ctxt.stack
  args <- printDeclList {typed = True} params
  stmt <- printStatement stmt
  pure $ vsep [ "package main"
              , ""
              , "func testFunc(" <+> args <+> ")" <++> ret <++> "{"
              , indent' 4 stmt
              , "}"
              , ""
              , "func main() {"
              , "}"
              ]


wrapExpr {ctxt} expr = do
  let params = enumerate $ asList ctxt.stack
  args <- printDeclList {typed = True} params
  expr <- printExpr expr
  let store = "temp :=" <++> expr
  pure $ vsep [ "package main"
              , ""
              , "func testFunc(" <+> args <+> ")" <++> "{"
              , indent' 4 store
              , indent' 4 "print(temp)"
              , "}"
              , ""
              , "func main() {"
              , "}"
              ]
