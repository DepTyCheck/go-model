module Language.Go.Derived.Statements

import public Language.Go

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

Language.Go.genStatements = deriveGen
