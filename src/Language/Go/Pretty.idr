module Language.Go.Pretty

import Data.Alternative
import Data.Fuel
import Data.List

import Language.Go

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

mutual
  printTy : {opts : _} -> GoType -> Doc opts
  printTy GoInt = "int"
  printTy GoBool = "bool"
  printTy (GoFunc $ MkFuncTy ss rs) =
    "func " <++> printTyOrTypes ss <++> printTyOrTypes rs
  -- @WHEN ASSIGNABLE_ANY
  -- @ printTy GoAny = "interface {}"
  -- @END ASSIGNABLE_ANY

  printTyOrTypes : {opts : _} -> GoTypes -> Doc opts
  printTyOrTypes [] = ""
  printTyOrTypes [ty] = assert_total printTy ty
  printTyOrTypes ts = assert_total $ tuple $ map printTy $ asList ts


printVar :  {opts : _} ->
            (decl : Declaration) ->
            Gen0 $ Doc opts
printVar (Declare kind name _) = pure $ line "\{show kind}\{show name}"

printVarTy :  {opts : _} ->
              (decl : Declaration) ->
              Gen0 $ Doc opts
printVarTy decl = pure $ !(printVar decl) <++> printTy decl.type

printParams : {opts : _} ->
              Block ->
              Gen0 $ Doc opts
printParams [] = pure ""
printParams [p] = printVarTy p
printParams (p :: ps) = pure $
                 !(printVarTy p) <+> "," <++> !(printParams ps)

Show (BuiltinFunc _ _) where
  show Print = "print"
  -- @WHEN EXTRA_BUILTINS
  -- @ show Max = "max"
  -- @ show Min = "min"
  -- @END EXTRA_BUILTINS

mutual
  printValues : (fuel : Fuel) ->
                {ctxt : Context} ->
                (knownNames : List String) =>
                {opts : _} ->
                {types : GoTypes} ->
                (values : ExprList ctxt types) ->
                Gen0 $ Doc opts
  printValues fuel Nil = pure ""
  printValues fuel [x] = printExpr fuel x
  printValues fuel (x::xs) = do
    x <- printExpr fuel x
    xs <- printValues fuel xs
    pure $ x <+> "," <++> xs


  printFuncCall : (fuel : Fuel) ->
                  {ctxt : Context} ->
                  (knownNames : List String) =>
                  {opts : _} ->
                  (f : Doc opts) ->
                  (args : Expr ctxt _) ->
                  Gen0 $ Doc opts
  printFuncCall fuel f args = do
    args <- printExpr fuel args
    pure $ f <+> "(" <+> args <+> ")"

  printInfix : (fuel : Fuel) ->
               {ctxt : Context} ->
               (knownNames : List String) =>
               {opts : _} ->
               (op : String) ->
               (lhv : Expr ctxt _) ->
               (rhv : Expr ctxt _) ->
               Gen0 $ Doc opts
  printInfix fuel op lhv rhv = do
      lhv <- printExpr fuel lhv
      rhv <- printExpr fuel rhv
      pure $ "(" <+> lhv <++> line op <++> rhv <+> ")"

  export
  printExpr :  (fuel :  Fuel) ->
               {ctxt : Context} ->
               (knownNames : List String) =>
               {opts : _} ->
               Expr ctxt ret -> Gen0 $ Doc opts

  printExpr fuel (GetLiteral $ MkInt x) = pure $ line $ show x

  printExpr fuel (GetLiteral $ MkBool True) = pure $ line "true"
  printExpr fuel (GetLiteral $ MkBool False) = pure $ line "false"

  -- @WHEN EXTRA_BUILTINS
  -- @ printExpr fuel (ApplyPrefix BoolNot arg) = do
    -- @ arg <- printExpr fuel arg
    -- @ pure $ "(!" <+> arg <+> ")"
  -- @ printExpr fuel (ApplyPrefix IntNeg arg) = do
    -- @ arg <- printExpr fuel arg
    -- @ pure $ "(-" <+> arg <+> ")"
  -- @END EXTRA_BUILTINS

  printExpr fuel (ApplyInfix IntAdd lhv rhv) = printInfix fuel "+" lhv rhv
  -- @WHEN EXTRA_BUILTINS
  -- @ printExpr fuel (ApplyInfix IntSub lhv rhv) = printInfix fuel "-" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntMul lhv rhv) = printInfix fuel "*" lhv rhv
  -- @ printExpr fuel (ApplyInfix BoolAnd lhv rhv) = printInfix fuel "&&" lhv rhv
  -- @ printExpr fuel (ApplyInfix BoolOr lhv rhv) = printInfix fuel "||" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntEq lhv rhv) = printInfix fuel "==" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntNE lhv rhv) = printInfix fuel "!=" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntLt lhv rhv) = printInfix fuel "<" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntLE lhv rhv) = printInfix fuel "<=" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntGt lhv rhv) = printInfix fuel ">" lhv rhv
  -- @ printExpr fuel (ApplyInfix IntGE lhv rhv) = printInfix fuel ">=" lhv rhv
  -- @END EXTRA_BUILTINS

  printExpr fuel (CallBuiltin f arg) = do
    printFuncCall fuel (line $ show f) arg

  printExpr fuel (AnonFunc {retTypes} paramBlock body) = do
    params <- printParams paramBlock
    body <- printStatement fuel body
    let rets = printTyOrTypes retTypes
    pure $ vsep [ "func" <++> "(" <+> params <+> ")" <++> rets <++> "{"
                , indent' 4 body
                , "}"
                ]

  -- printExpr fuel (GetVar decl) = printVar decl

  -- printExpr fuel (CallNamed f args) = do
  --   f <- printVar f
  --   args <- printExpr fuel args
  --   pure $ f <+> "(" <+> args <+> ")"

  printExpr fuel (MultiVal vals) = printValues fuel vals

  -- @WHEN IF_STMTS
  -- @ printIf : (fuel : Fuel) ->
            -- @ {ctxt, ctxtThen, ctxtElse : Context} ->
            -- @ (knownNames : List String) =>
            -- @ {opts : _} ->
            -- @ (test : Expr ctxt [GoBool]) ->
            -- @ (th : Statement ctxtThen) ->
            -- @ (el : Statement ctxtElse) ->
            -- @ Gen0 $ Doc opts

  -- @ printIf fuel test th el = do
    -- @ test' <- printExpr fuel test
    -- @ th' <- assert_total printStatement fuel th
    -- @ let skipElse = isEmpty el && !(chooseAnyOf Bool)
    -- @ el' <- if skipElse
             -- @ then pure empty
             -- @ else do
               -- @ body <- assert_total printStatement fuel el
               -- @ pure $ "} else {" `vappend` indent' 4 body
    -- @ let top = hangSep 0 ("if" <++> test') "{"
    -- @ pure $ vsep [ top
                -- @ , indent' 4 th'
                -- @ , el'
                -- @ , "}"
                -- @ ]
  -- @END IF_STMTS

  export
  printStatement : (fuel : Fuel) ->
                   {opts : _} ->
                   {ctxt : Context} ->
                   (knownNames : List String) =>
                   Statement ctxt -> Gen0 $ Doc opts

  printStatement fuel JustStop = pure ""

  printStatement fuel (Return res) = do
    resText <- printExpr fuel res
    pure $ "return" <++> resText

  printStatement fuel (VoidExpr expr cont) = do
    e <- printExpr fuel expr
    contText <- printStatement fuel cont
    pure $ e `vappend` contText

  -- @WHEN IF_STMTS
  -- @ printStatement fuel (InnerIf {ctxtThen} {ctxtElse} test th el cont) = do
    -- @ ifText <- printIf fuel test th el
    -- @ contText <- printStatement fuel cont
    -- @ pure $ ifText `vappend` contText

  -- @ printStatement fuel (TermIf test th el) = do
    -- @ ifText <- printIf fuel test th el
    -- @ pure ifText
  -- @END IF_STMTS

  printStatement fuel (DeclareVar newName ty initial cont) = do
    varText <- printVar (Declare Var newName ty)
    initValText <- printExpr fuel initial
    let lineText = "var" <++> varText <++> "=" <++> initValText
    let lineText2 = "_" <++> "=" <++> varText
    contText <- printStatement fuel cont
    pure $ (lineText `vappend` lineText2) `vappend` contText


export
printGo : (fuel : Fuel) ->
          {ctxt : Context} ->
          (knownNames : List String) ->
          {opts : _} ->
          Statement ctxt -> Gen0 $ Doc opts
printGo fuel {ctxt} knownNames block = do
  content <- printStatement fuel block
  let ret = printTyOrTypes ctxt.returns
  pure $ vsep [ "package main"
              , ""
              , "func testFunc()" <++> ret <++> "{"
              , indent' 4 content
              , "}"
              , ""
              , "func main() {"
              , "    testFunc()"
              , "}"
              ]
