module Language.Go.Pretty

import Data.Alternative
import Data.Fuel
import Data.List

import Language.Go

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy
import Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen


mutual
  printTy : {opts : _} -> GoType -> Doc opts
  printTy GoInt = "int"
  printTy GoBool = "bool"
  printTy (GoFunc $ MkFuncTy ss rs) =
    "func " <++> printTyOrTypes ss <++> printTyOrTypes rs
  printTy GoAny = "interface {}"

  printTyOrTypes : {opts : _} -> GoTypes -> Doc opts
  printTyOrTypes [] = ""
  printTyOrTypes [ty] = assert_total printTy ty
  printTyOrTypes ts = assert_total $ tuple $ map printTy $ asList ts



printVar :  {opts : _} ->
            (decl : Declaration) ->
            Gen0 $ Doc opts
printVar (Declare kind name _) = pure $ line "\{show kind}\{show name}"

mutual
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

  printExpr fuel (IntLiteral x) = pure $ line $ show x
  printExpr fuel (BoolLiteral True) = pure $ line "true"
  printExpr fuel (BoolLiteral False) = pure $ line "false"
  printExpr fuel (GetVar decl) = printVar decl
  -- printExpr fuel (CallNamed f args) = do
  --   f <- printVar f
  --   args <- printExpr fuel args
  --   pure $ f <+> "(" <+> args <+> ")"

  printExpr fuel (SpecForm $ Print arg) = do
    arg <- printExpr fuel arg
    pure $ "print(" <+> arg <+> ")"

  -- printExpr fuel (SpecForm $ BoolNot arg) = do
  --   arg <- printExpr fuel arg
  --   pure $ "(!" <+> arg <+> ")"

  printExpr fuel (ApplyInfix IntAdd lhv rhv) = printInfix fuel "+" lhv rhv
  printExpr fuel (ApplyInfix IntSub lhv rhv) = printInfix fuel "-" lhv rhv
  printExpr fuel (ApplyInfix IntMul lhv rhv) = printInfix fuel "*" lhv rhv
  printExpr fuel (ApplyInfix BoolAnd lhv rhv) = printInfix fuel "&&" lhv rhv
  printExpr fuel (ApplyInfix BoolOr lhv rhv) = printInfix fuel "||" lhv rhv

  printIf : (fuel : Fuel) ->
            {ctxt, ctxtThen, ctxtElse : Context} ->
            (knownNames : List String) =>
            {opts : _} ->
            (test : Expr ctxt [GoBool]) ->
            (th : Statement ctxtThen) ->
            (el : Statement ctxtElse) ->
            Gen0 $ Doc opts

  printIf fuel test th el = do
    test' <- printExpr fuel test
    th' <- assert_total printStatement fuel th
    let skipElse = isEmpty el && !(chooseAnyOf Bool)
    el' <- if skipElse
             then pure empty
             else do
               body <- assert_total printStatement fuel el
               pure $ "} else {" `vappend` indent' 4 body
    let top = hangSep 0 ("if" <++> test') "{"
    pure $ vsep [ top
                , indent' 4 th'
                , el'
                , "}"
                ]

  export
  printStatement : (fuel : Fuel) ->
               {ctxt : Context} ->
               (knownNames : List String) =>
               {opts : _} ->
               Statement ctxt -> Gen0 $ Doc opts

  printStatement fuel JustStop = pure ""

  printStatement fuel (Return res) = do
    resText <- printExpr fuel res
    pure $ "return" <++> resText

  printStatement fuel (VoidExpr expr cont) = do
    e <- printExpr fuel expr
    contText <- printStatement fuel cont
    pure $ e `vappend` contText

  printStatement fuel (InnerIf {ctxtThen} {ctxtElse} test th el cont) = do
    ifText <- printIf fuel test th el
    contText <- printStatement fuel cont
    pure $ ifText `vappend` contText

  printStatement fuel (TermIf test th el) = do
    ifText <- printIf fuel test th el
    pure ifText

  printStatement fuel (DeclareVar name ty initial {newCtxt} cont) = do
    initValText <- pure "WTF" -- printExpr fuel initial
    varText <- printVar (Declare Var name ty)
    let lineText = "var" <++> varText <++> "=" <++> initValText
    let lineText2 = "_" <++> "=" <++> varText
    contText <- printStatement {ctxt = newCtxt} fuel cont
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
