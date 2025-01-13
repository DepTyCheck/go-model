module Language.Go.Pretty

import Data.Fuel
import Data.So
import Data.SortedSet

import Language.Go

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

-- mutual
--   public export
--   data UniqNames : (ctxt : Context) -> Type where
--     [search ctxt]
--     Empty   : UniqNames [<]
--     JustNew : (ss : UniqNames ctxt) => (s : String) -> (0 _ : NameIsNew ctxt ss s) => UniqNames ctxt
--     NewDef  : (ss : UniqNames ctxt) => (s : String) -> (0 _ : NameIsNew ctxt ss s) => UniqNames (ctxt :< def)

--   public export
--   data NameIsNew : (ctxt : Context) -> UniqNames ctxt -> String -> Type where
--     E : NameIsNew [<] Empty x
--     J : (0 _ : So $ x /= s) -> NameIsNew ctxt ss x -> NameIsNew ctxt (JustNew @{ss} s @{sub}) x
--     D : (0 _ : So $ x /= s) -> NameIsNew ctxt ss x -> NameIsNew (ctxt :< def) (NewDef @{ss} s @{sub}) x

-- reservedKeywords : SortedSet String

-- mutual
--   rawNewName : Fuel ->
--                (Fuel -> Gen MaybeEmpty String) =>
--                (ctxt : Context) ->
--                (names : UniqNames ctxt) ->
--                Gen MaybeEmpty (s ** NameIsNew ctxt names s)

--   genNewName : Fuel ->
--                Gen MaybeEmpty String ->
--                (ctxt : Context) ->
--                (names : UniqNames ctxt) ->
--                Gen MaybeEmpty (s ** NameIsNew ctxt names s)
--   genNewName fuel genStr ctxt names = do
--     nn@(nm ** _) <- rawNewName fuel @{const genStr} ctxt names
--     if reservedKeywords `contains'` nm
--       then assert_total $ genNewName fuel genStr ctxt names
--       else pure nn

-- goNamesGen : Gen0 String
-- goNamesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

-- export
-- prettyName : UniqNames ctxt -> IndexIn ctxt -> String
-- prettyName (JustNew @{ss} _) i         = prettyName ss i
-- prettyName (NewDef s)        Here      = s
-- prettyName (NewDef @{ss} _)  (There i) = prettyName ss i

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

