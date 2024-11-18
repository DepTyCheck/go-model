module Language.Go.Pretty

import Data.Alternative
import Data.Fuel
import Data.SnocList
import Data.So
import Data.SortedSet
import Data.Vect

import Language.Go

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

mutual
  public export
  data UniqNames : (ctxt : Context) -> Type where
    [search ctxt]
    Empty   : UniqNames [<]
    JustNew : (ss : UniqNames ctxt) => (s : String) -> (0 _ : NameIsNew ctxt ss s) => UniqNames ctxt
    NewDef  : (ss : UniqNames ctxt) => (s : String) -> (0 _ : NameIsNew ctxt ss s) => UniqNames (ctxt :< def)

  public export
  data NameIsNew : (ctxt : Context) -> UniqNames ctxt -> String -> Type where
    E : NameIsNew [<] Empty x
    J : (0 _ : So $ x /= s) -> NameIsNew ctxt ss x -> NameIsNew ctxt (JustNew @{ss} s @{sub}) x
    D : (0 _ : So $ x /= s) -> NameIsNew ctxt ss x -> NameIsNew (ctxt :< def) (NewDef @{ss} s @{sub}) x

reservedKeywords : SortedSet String

mutual
  rawNewName : Fuel ->
               (Fuel -> Gen MaybeEmpty String) =>
               (ctxt : Context) ->
               (names : UniqNames ctxt) ->
               Gen MaybeEmpty (s ** NameIsNew ctxt names s)

  genNewName : Fuel ->
               Gen MaybeEmpty String ->
               (ctxt : Context) ->
               (names : UniqNames ctxt) ->
               Gen MaybeEmpty (s ** NameIsNew ctxt names s)
  genNewName fuel genStr ctxt names = do
    nn@(nm ** _) <- rawNewName fuel @{const genStr} ctxt names
    if reservedKeywords `contains'` nm
      then assert_total $ genNewName fuel genStr ctxt names
      else pure nn

goNamesGen : Gen0 String
goNamesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

export
prettyName : UniqNames ctxt -> IndexIn ctxt -> String
prettyName (JustNew @{ss} _) i         = prettyName ss i
prettyName (NewDef s)        Here      = s
prettyName (NewDef @{ss} _)  (There i) = prettyName ss i

-- -- Returned vect has a reverse order; I'd like some `SnocVect` here.
-- newVars : NamesRestrictions =>
--           {l : _} -> {funs : _} -> {vars : _} ->
--           Fuel ->
--           (newNames : Gen0 String) ->
--           (extraVars : _) -> UniqNames l funs vars ->
--           Gen0 (UniqNames l funs (vars ++ extraVars), Vect extraVars.length (String, Ty))
-- newVars _  _ [<] names = pure (names, [])
-- newVars fuel newNames (vs:<v) names = do
--   (names', vts) <- newVars fuel newNames vs names
--   (nm ** _) <- genNewName {l} fuel newNames _ _ names'
--   pure (NewVar @{names'} nm, (nm, v)::vts)

-- public export
-- 0 PP : SupportedLanguage -> Type
-- PP language = {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
--               (names : UniqNames language funs vars) =>
--               Fuel ->
--               Stmts funs vars retTy -> Gen0 $ Doc opts

-- luaNamesGen : Gen0 String
-- luaNamesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

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

-- withCont : {opts : _} -> (cont : Doc opts) -> (stmt : Doc opts) -> Gen0 (Doc opts)
-- withCont cont stmt =
--   pure $ stmt `vappend` cont

-- printStmts fuel (NewV ty mut initial cont) = do
--   (name ** _) <- genNewName fuel newNames _ _ names
--   lhv <- newVarLhv name mut
--   rhv <- printExpr fuel Nothing initial
--   withCont !(printStmts fuel cont) $ hangSep' 2 (lhv <++> "=") rhv

-- printStmts fuel (NewF sig body cont) = do
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
--   cont' <- printStmts fuel cont
--   withCont cont' $ vsep [ hints
--                         , fnHeader
--                         , indent' 2 fnBody
--                         , "end"
--                         ]

-- printStmts fuel ((#=) lhv rhv cont) = do
--   let lhv' = line (varName names lhv) <++> "="
--   rhv' <- printExpr fuel Nothing rhv
--   withCont !(printStmts fuel cont) $ hangSep' 2 lhv' rhv'


-- printStmts fuel (Call n x cont) = do
--   call <- printFunCall fuel Nothing n x
--   withCont !(printStmts fuel cont) call

-- printStmts fuel (Ret res) =
--   pure $ "return" <++> !(printExpr fuel Nothing res)

export
printExpr :  (fuel :  Fuel) ->
             {ctxt : Context} -> {cont : Types} -> {opts : _} ->
             (names : UniqNames ctxt) =>
             (newNames : Gen0 String) =>
             Expr ctxt cont -> Gen0 $ Doc opts

export
printBlock : (fuel : Fuel) ->
             {ctxt : Context} -> {cont : Types} -> {bo : _} -> {opts : _} ->
             (names : UniqNames ctxt) =>
             (newNames : Gen0 String) =>
             Block ctxt cont bo -> Gen0 $ Doc opts

export
printIf : (fuel : Fuel) ->
          {ctxt : Context} -> {cont : Types} -> {bo : _} -> {opts : _} ->
          (names : UniqNames ctxt) =>
          (newNames : Gen0 String) =>
          Expr ctxt [<Bool'] ->
          Block ctxt cont bo -> Block ctxt cont bo ->
          Gen0 $ Doc opts

printExpr fuel (Const lit) = pure $ line $ show lit

printIf fuel test th el = do
  test' <- printExpr fuel test
  th' <- printBlock fuel th
  let skipElse = isNop el && !(chooseAnyOf Bool)
  el' <- if skipElse
           then pure empty
           else do
             body <- printBlock @{names} @{newNames} fuel el
             pure $ "} else {" `vappend` indent' 2 body
  let top = hangSep 0 ("if" <++> test') "{"
  pure $ vsep [ top
              , indent' 2 th'
              , el'
              , "}"
              ]

printBlock fuel End = pure ""

printBlock fuel (Ret res) = do
  pure $ "return" <++> !(printExpr fuel res)

printBlock fuel (TermIf test th el) = do
  printIf fuel test th el

printBlock fuel (SimpleIf test th el next) = do
  this <- printIf fuel test th el
  next' <- printBlock fuel next
  pure $ this `vappend` next'

public export
printGo : (fuel : Fuel) ->
          {ctxt : Context} -> {cont : Types} -> {bo : _} -> {opts : _} ->
          (names : UniqNames ctxt) =>
          Block ctxt cont bo -> Gen0 $ Doc opts
printGo fuel = printBlock fuel {names} {newNames = goNamesGen}
