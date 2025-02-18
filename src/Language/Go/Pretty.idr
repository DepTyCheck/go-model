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
  printTy : {opts : _} -> Ty -> Doc opts
  printTy Int' = "int"
  printTy Bool' = "bool"
  printTy (Func' $ MkFuncTy ss rs) =
    "func " <++> printTyOrTypes ss <++> printTyOrTypes rs
  printTy Any' = "interface {}"

  printTyOrTypes : {opts : _} -> Types -> Doc opts
  printTyOrTypes [] = ""
  printTyOrTypes [ty] = assert_total printTy ty
  printTyOrTypes ts = assert_total $ tuple $ map printTy $ asList ts



printVar :  {ctxt : Context} ->
            (knownNames : List String) =>
            {opts : _} ->
            (depth : Fin ctxt.depth) -> Gen0 $ Doc opts
printVar depth = let
                   dfn = dig ctxt.definitions depth
                   idx = dfn.defName
                   pref = show dfn.defKind
                   text = case inBounds idx knownNames of
                               Yes _ => List.index idx knownNames
                               No _ => pref ++ show idx
                 in pure $ line text -- <++> line "/*" <++> line (printTy dfn.defTy) <++> line "*/"

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
  printExpr fuel (GetVar depth) = printVar depth
  printExpr fuel (CallNamed f args) = do
    f <- printVar f
    args <- printExpr fuel args
    pure $ f <+> "(" <+> args <+> ")"

  printExpr fuel (SpecForm $ Print arg) = do
    arg <- printExpr fuel arg
    pure $ "print(" <+> arg <+> ")"

  printExpr fuel (SpecForm $ BoolNot arg) = do
    arg <- printExpr fuel arg
    pure $ "(!" <+> arg <+> ")"

  printExpr fuel (SpecForm $ IntAdd lhv rhv) = printInfix fuel "+" lhv rhv
  printExpr fuel (SpecForm $ IntSub lhv rhv) = printInfix fuel "-" lhv rhv
  printExpr fuel (SpecForm $ IntMul lhv rhv) = printInfix fuel "*" lhv rhv
  printExpr fuel (SpecForm $ BoolAnd lhv rhv) = printInfix fuel "&&" lhv rhv
  printExpr fuel (SpecForm $ BoolOr lhv rhv) = printInfix fuel "||" lhv rhv

  printIf : (fuel : Fuel) ->
            {ctxt, ctxtThen, ctxtElse : Context} ->
            (knownNames : List String) =>
            {opts : _} ->
            (test : Expr ctxt [Bool']) ->
            (th : Block ctxtThen) ->
            (el : Block ctxtElse) ->
            Gen0 $ Doc opts

  printIf fuel test th el = do
    test' <- printExpr fuel test
    th' <- assert_total printBlock fuel th
    let skipElse = isEmpty el && !(chooseAnyOf Bool)
    el' <- if skipElse
             then pure empty
             else do
               body <- assert_total printBlock fuel el
               pure $ "} else {" `vappend` indent' 4 body
    let top = hangSep 0 ("if" <++> test') "{"
    pure $ vsep [ top
                , indent' 4 th'
                , el'
                , "}"
                ]

  export
  printBlock : (fuel : Fuel) ->
               {ctxt : Context} ->
               (knownNames : List String) =>
               {opts : _} ->
               Block ctxt -> Gen0 $ Doc opts

  printBlock fuel JustStop = pure ""

  printBlock fuel (Return res) = do
    resText <- printExpr fuel res
    pure $ "return" <++> resText

  printBlock fuel (VoidExpr expr cont) = do
    e <- printExpr fuel expr
    contText <- printBlock fuel cont
    pure $ e `vappend` contText

  printBlock fuel (InnerIf {ctxtThen} {ctxtElse} test th el cont) = do
    ifText <- printIf fuel test th el
    contText <- printBlock fuel cont
    pure $ ifText `vappend` contText

  printBlock fuel (TermIf test th el) = do
    ifText <- printIf fuel test th el
    pure ifText

  printBlock fuel (InitVar {newCtxt} {pr} newTy initVal cont) = do
    let MkAddDefinition = pr
    initValText <- printExpr fuel initVal
    varText <- printVar {ctxt = newCtxt} FZ
    let lineText = "var" <++> varText <++> "=" <++> initValText
    let lineText2 = "_" <++> "=" <++> varText
    contText <- printBlock fuel cont
    pure $ (lineText `vappend` lineText2) `vappend` contText


export
printGo : (fuel : Fuel) ->
          {ctxt : Context} ->
          (knownNames : List String) ->
          {opts : _} ->
          Block ctxt -> Gen0 $ Doc opts
printGo fuel {ctxt} knownNames block = do
  content <- printBlock fuel block
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
