module Language.Go.Derived

import public Language.Go.Model
import public Language.Go.Derived.Tuning

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

-- Language.Go.genStatements = deriveGen

Language.Go.Model.genExprs = deriveGen
