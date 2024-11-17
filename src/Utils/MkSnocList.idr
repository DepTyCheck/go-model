module Utils.MkSnocList

import Data.Fuel
import Data.Nat
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE
import Generics.Derive

import Language.Reflection
import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops
import Language.Reflection.Util

import Test.DepTyCheck.Gen
import Text.PrettyPrint.Bernardy

%language ElabReflection


public export
mkSnocList : (of_ : TTImp) -> (snocListName : String) -> Elab ()
mkSnocList of_ snocListName = do
  let snocList = varStr snocListName

  let linName = "Lin"
  let lin = var linName
  let linCon : ITy = mkTy linName snocList
  let snocName = ":<"
  let snoc = var (UN $ Basic snocName)
  let snocCon : ITy = mkTy (fromString snocName) $
    arg snocList .-> arg of_ .-> snocList
  let dataDef = simpleData Public (fromString snocListName) [ linCon, snocCon ]

  let emptyClause = var `{length} .$ lin .= `(0)
  let snocClause = var `{length} .$ (snoc .$ bindVar "xs" .$ implicitTrue) .=
    `(length xs + 1)
  let lengthDef =
    [ public' `{length} $ arg snocList .-> `(Nat)
    , def `{length} [emptyClause, snocClause]
    , public' `{(.length)} $ arg snocList .-> `(Nat)
    , def `{(.length)} [ var `{(.length)} .= `(length) ]
    ]

  -- let namedArg = \x => MkArg MW ExplicitArg (Just x) snocList

  -- let snocNameQ = snocListName ++ ".(:<)"
  -- let snocQ = var (UN $ Basic snocNameQ)
  -- let biinjImplName = UN $ Basic $ "biinjective" ++ snocListName
  -- let biinjImpl = var biinjImplName
  -- let biinjImplClaim = private' biinjImplName $
  --     arg (var "=" .$ (snocQ .$ bindVar "x" .$ bindVar "v") .$ (snocQ .$ bindVar "y" .$ bindVar "w")) .->
  --       (var "=" .$ )
  -- let decEqImplName = UN $ Basic $ "decEq" ++ snocListName
  -- let decEqImpl = var decEqImplName
  -- let decEqImplClauses =
  --   [ decEqImpl .$ lin .$ lin .= `(Yes Refl)
  --   , decEqImpl .$
  --     (snoc .$ bindVar "xs" .$ bindVar "x") .$
  --     (snoc .$ bindVar "ys" .$ bindVar "y") .=
  --       (var `{decEqCong2} .$ (decEqImpl .$ var `{xs} .$ var `{ys}) .$ (var "decEq" .$ var `{x} .$ var `{y}))
  --   , decEqImpl .$
  --     (snoc .$ implicitTrue .$ implicitTrue) .$ lin .=
  --       `(No $ \case Refl impossible)
  --   , decEqImpl .$
  --       lin .$ (snoc .$ implicitTrue .$ implicitTrue) .=
  --         `(No $ \case Refl impossible)
  --   ]
  -- let decEqImplClaim = private' decEqImplName $ namedArg "x" .-> namedArg "y" .-> `(Dec (x = y))
  -- let decEqImplDef = [ decEqImplClaim
  --                    , def decEqImplName decEqImplClauses
  --                    ]

  declare $
    [ dataDef ]
    ++ lengthDef
  -- declare [ INamespace emptyFC (MkNS [snocListName]) $
  --   [ dataDef ]
  --   ++ lengthDef
    -- ++ decEqImplDef
  derive (fromString snocListName) [DE.Eq]
