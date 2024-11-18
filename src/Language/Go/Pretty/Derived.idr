module Language.Go.Pretty.Derived

import public Language.Go
import public Language.Go.Pretty

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Language.Go.Pretty.rawNewName = deriveGen
