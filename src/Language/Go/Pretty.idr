module Language.Go.Pretty

import Data.Alternative
import Data.Fuel
import Data.List

import Language.Go

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen


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
                 in pure $ line text

mutual
  printExpr :  (fuel :  Fuel) ->
               {ctxt : Context} ->
               (knownNames : List String) =>
               {opts : _} ->
               Expr ctxt ret -> Gen0 $ Doc opts

  printExpr fuel (IntLiteral x) = pure $ line $ show x
  printExpr fuel (BoolLiteral True) = pure $ line "true"
  printExpr fuel (BoolLiteral False) = pure $ line "false"
  printExpr fuel (GetVar depth) = printVar depth

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


public export
printGo : (fuel : Fuel) ->
          {ctxt : Context} ->
          (knownNames : List String) ->
          {opts : _} ->
          Block ctxt -> Gen0 $ Doc opts
printGo fuel knownNames block = do
  content <- printBlock fuel block
  pure $ vsep [ "package main"
              , ""
              , "func testFunc(someIntVar int) int {"
              , indent' 4 content
              , "}"
              , ""
              , "func main() {"
              , "    testFunc(42)"
              , "}"
              ]
