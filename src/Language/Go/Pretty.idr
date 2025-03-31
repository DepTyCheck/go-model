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
printTypeList : GoTypes -> Printer

export
printName : Kind -> GoName -> Printer

export
printDecl : {default False typed : Bool} -> Declaration -> Printer

export
printDeclList : {default False typed : Bool} -> Block -> Printer

export
funcCall : {opts : _} -> (f, args : Doc opts) -> Doc opts

export
printExprList : forall ts. {ctxt : Context} -> ExprList ctxt ts -> Printer

export
printExpr : forall rets.
            {ctxt : Context} ->
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

printType (GoFunc params rets) {opts} = do
  params <- printTypeList params
  let params = enclose "(" ")" params
  rets <- printNoneOneOrList (assert_total printType) (asList rets)
  pure $ "func" <+> params <++> rets

-- @WHEN ASSIGNABLE_ANY
-- @ printType GoAny = pure "interface {}"
-- @END ASSIGNABLE_ANY


printTypeList ts = printList (assert_total printType) (asList ts)


printName kind (MkName n) = do
  let pre = case kind of
                 Var => "v"
                 Const => "c"
                 Func => "f"
  pure $ line $ pre <+> show n


printDecl {typed} (Declare kind name ty) {opts} = do
  name <- printName kind name {opts}
  if typed
     then do
       ty <- printType ty
       pure $ name <++> ty
     else
       pure name


printDeclList {typed} vs = printList (printDecl {typed}) (asList vs)


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


Show (BuiltinFunc _ _) where
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

printExpr (AnonFunc {retTypes} paramBlock body) = do
  params <- printDeclList {typed = True} paramBlock
  body <- printStatement body
  rets <- printNoneOneOrList printType (asList retTypes)
  let holes = map (const "_") $ asList paramBlock
  use <- case holes of
              [] => pure ""
              _  => do
                holes <- printList (\h => pure $ line h) holes
                vars <- printDeclList {typed = False} paramBlock
                pure $ holes <++> "=" <++> vars
  pure $ vsep [ "func" <++> "(" <+> params <+> ")" <++> rets <++> "{"
              , indent' 4 use
              , indent' 4 body
              , "}"
              ]

printExpr (CallNamed kind name _ args) = do
  args <- printExprList args
  fn <- printName kind name
  pure $ funcCall fn args

printExpr (GetDecl kind name _) = printName kind name

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

printStatement (DeclareVar newName ty initial cont) = do
  var <- printDecl (Declare Var newName ty)
  initial <- printExpr initial
  let decl = "var" <++> var <++> "=" <++> initial
  let use = "_" <++> "=" <++> var
  cont <- printStatement cont
  pure $ vsep [ decl
              , use
              , cont
              ]


wrapStatement {ctxt} stmt = do
  ret <- printTypeList ctxt.returns
  args <- printDeclList {typed = True} ctxt.blocks.top
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
  args <- printDeclList {typed = True} ctxt.blocks.top
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
