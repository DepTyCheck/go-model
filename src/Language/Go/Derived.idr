module Language.Go.Derived

import public Language.Go.Model
import public Language.Go.Derived.Tuning

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

-- @WHEN GEN_STMT
Language.Go.Model.genStatements = deriveGen
-- @UNLESS GEN_STMT
-- @ Language.Go.Model.genExprs = deriveGen
-- @END GEN_STMT

