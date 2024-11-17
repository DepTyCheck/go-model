module Language.Go.Derived

import public Language.Go

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Language.Go.genStmts = deriveGen
