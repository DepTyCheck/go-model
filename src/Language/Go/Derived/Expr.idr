module Language.Go.Derived.Expr

import public Language.Go

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

Language.Go.genExprs = deriveGen
