module Language.Go.Pretty.Go

import Data.Alternative
import Data.Fuel
import Data.SnocList
import Data.So
import Data.SortedSet
import Data.Vect

import Language.Go
import Language.Go.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

-- printTy : Ty -> Doc opts
-- printTy Int'  = "number"
-- printTy Bool' = "boolean"

-- NamesRestrictions where
--   reservedKeywords = fromList
--     [ "and",       "break",     "do",        "else",      "elseif",    "end"
--     , "false",     "for",       "function",  "goto",      "if",        "in"
--     , "local",     "nil",       "not",       "or",        "repeat",    "return"
--     , "then",      "true",      "until",     "while"
--     ]

-- Priority : Type
-- Priority = Fin 12

-- priorities : List (String, Priority)
-- priorities = [ ("or", 11)
--              , ("and", 10)
--              , ("<", 9), (">", 9), ("<=", 9), (">=", 9), ("~=", 9), ("==", 9)
--              , ("|", 8)
--              , ("~", 7)
--              , ("&", 6)
--              , ("<<", 5), (">>", 5)
--              , ("..", 4)
--              , ("+", 3), ("-", 3)
--              , ("*", 2), ("/", 2), ("//", 2), ("%", 2)
--              , ("not", 1), ("#", 1), ("-", 1), ("~", 1)
--              , ("^", 0)
--              ]

-- priority : String -> Maybe Priority
-- priority func = lookup func priorities

-- printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
--                (names : UniqNames Lua5_4 funs vars) =>
--                Fuel ->
--                (lastPriority : Maybe Priority) ->
--                IndexIn funs -> ExprsSnocList funs vars argTys ->
--                Gen0 $ Doc opts
-- printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
--              (names : UniqNames Lua5_4 funs vars) =>
--              (newNames : Gen0 String) =>
--              Fuel ->
--              Stmts funs vars retTy -> Gen0 $ Doc opts

-- printExpr fuel _ (C $ I x) = pure $ line $ show x
-- printExpr fuel _ (C $ B True) = pure "true"
-- printExpr fuel _ (C $ B False) = pure "false"
-- printExpr fuel _ (V n) = pure $ line $ varName names n
-- printExpr fuel lastPrior (F n x) = printFunCall fuel lastPrior n x

-- addCommas : {opts : _} -> List (Doc opts) -> List (Doc opts)
-- addCommas [] = []
-- addCommas [x] = [x]
-- addCommas (x::xs) = (x <+> comma) :: addCommas xs

-- printFunCall fuel lastPrior fun args = do
--   let name = funName names fun
--   let thisPrior = priority name
--   let addParens = !(chooseAnyOf Bool)
--                    || isJust lastPrior && thisPrior >= lastPrior
--   args' <- for (toList $ getExprs args) (\(Evidence _ e) => assert_total printExpr fuel Nothing e)
--   case (isFunInfix names fun, args') of
--     (True, [lhv, rhv]) => do
--        pure $ parenthesise addParens $ hangSep 2 (lhv <++> line name) rhv
--     (_, [x]) => do
--        -- note: two minus signs may be interpreted as a comment
--        pure $ parenthesise addParens $ line name
--          <+> when (name == "not" || name == "-") space
--          <+> x
--     (_, _) => do
--       let argsWithCommas = sep' $ addCommas args'
--       let applyShort = line name <+> "(" <+> argsWithCommas <+> ")"
--       let applyLong = vsep [ line name <+> "("
--                            , indent 2 argsWithCommas
--                            , ")"
--                            ]
--       pure $ ifMultiline applyShort applyLong

-- newVarLhv : {opts : _} -> (name : String) -> (mut : Mut) -> Gen0 $ Doc opts
-- newVarLhv name mut = do
--   let attr = case mut of
--                Mutable => empty
--                Immutable => space <+> angles "const"
--   pure $ "local" <++> line name <+> attr

-- withCont : {opts : _} -> (ret : Doc opts) -> (stmt : Doc opts) -> Gen0 (Doc opts)
-- withCont ret stmt =
--   pure $ stmt `vappend` ret

-- printStmts fuel (NewV ty mut initial ret) = do
--   (name ** _) <- genNewName fuel newNames _ _ names
--   lhv <- newVarLhv name mut
--   rhv <- printExpr fuel Nothing initial
--   withCont !(printStmts fuel ret) $ hangSep' 2 (lhv <++> "=") rhv

-- printStmts fuel (NewF sig body ret) = do
--   (name ** _) <- genNewName fuel newNames _ _ names
--   (localNames, funArgs) <- newVars fuel newNames _ names
--   let funArgs' = reverse (toList funArgs)
--   let argHints = funArgs' <&> \(name, ty) =>
--                  the (Doc opts) "---@param" <++> line name <++> printTy ty
--   let hints = vsep $ case sig.To of
--                 Just retTy => argHints ++ ["---@return" <++> printTy retTy]
--                 Nothing => argHints
--   let argNames = funArgs' <&> \(name, _) => the (Doc opts) (line name)
--   let argList = sep' $ addCommas argNames
--   let fnHeaderShort = "local" <++> "function" <++> (line name) <+>
--                       "(" <+> argList <+> ")"
--   let fnHeaderLong = vsep [ "function" <++> (line name) <+> "("
--                           , indent 2 argList
--                           , ")"
--                           ]
--   let fnHeader = ifMultiline fnHeaderShort fnHeaderLong
--   fnBody <- printStmts @{localNames} fuel body
--   ret' <- printStmts fuel ret
--   withCont ret' $ vsep [ hints
--                         , fnHeader
--                         , indent' 2 fnBody
--                         , "end"
--                         ]

-- printStmts fuel ((#=) lhv rhv ret) = do
--   let lhv' = line (varName names lhv) <++> "="
--   rhv' <- printExpr fuel Nothing rhv
--   withCont !(printStmts fuel ret) $ hangSep' 2 lhv' rhv'


-- printStmts fuel (Call n x ret) = do
--   call <- printFunCall fuel Nothing n x
--   withCont !(printStmts fuel ret) call

-- printStmts fuel (Ret res) =
--   pure $ "return" <++> !(printExpr fuel Nothing res)

printVar :  {ctxt : Context} -> {opts : _} ->
            (depth : Depth ctxt.definitions) -> Gen0 $ Doc opts
printVar depth = pure $ line $ show $ dig ctxt.definitions depth

mutual
  printExpr :  (fuel :  Fuel) ->
               {ctxt : Context} -> {opts : _} ->
               -- (names : UniqNames ctxt) =>
               -- (newNames : Gen0 String) =>
               Expr ctxt ret -> Gen0 $ Doc opts

  printExpr fuel (IntLiteral x) = pure $ line $ show x
  printExpr fuel (BoolLiteral True) = pure $ line "true"
  printExpr fuel (BoolLiteral False) = pure $ line "false"
  printExpr fuel (GetVar depth) = printVar depth

  printIf : (fuel : Fuel) ->
            {ctxt : Context} ->
            {opts : _} ->
            -- (names : UniqNames ctxt) =>
            -- (newNames : Gen0 String) =>
            (test : Expr ctxt [<Bool']) ->
            (th : Block ctxt _) ->
            (el : Block ctxt _) ->
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
               {ctxt : Context} -> {opts : _} ->
               -- (names : UniqNames ctxt) =>
               -- (newNames : Gen0 String) =>
               Block ctxt _ -> Gen0 $ Doc opts

  printBlock fuel JustStop = pure ""

  printBlock fuel (Return res) = do
    resText <- printExpr fuel res
    pure $ "return" <++> resText

  printBlock fuel (InnerIf test th el cont) = do
    ifText <- printIf fuel test th el
    contText <- printBlock fuel cont
    pure $ ifText `vappend` contText

  printBlock fuel (TermIf test th el) = do
    ifText <- printIf fuel test th el
    pure ifText

  printBlock fuel (InitVar {newCtxt} {pr} newTy initVal cont) = do
    let NewDeBruijn = pr
    initValText <- printExpr fuel initVal
    varText <- printVar {ctxt = newCtxt} Z
    let lineText = "var" <++> varText <++> "=" <++> initValText
    contText <- printBlock fuel cont
    pure $ lineText `vappend` contText


public export
printGo : (fuel : Fuel) ->
          {ctxt : Context} -> {opts : _} ->
          -- (names : UniqNames ctxt) =>
          Block ctxt True -> Gen0 $ Doc opts
printGo fuel = printBlock fuel -- {names} {newNames = goNamesGen}
