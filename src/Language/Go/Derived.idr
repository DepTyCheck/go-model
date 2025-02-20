module Language.Go.Derived

import public Language.Go

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

Language.Go.genStatements = deriveGen

-- Language.Go.genExprs = deriveGen
