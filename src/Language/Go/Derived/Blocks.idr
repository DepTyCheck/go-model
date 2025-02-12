module Language.Go.Derived.Blocks

import public Language.Go

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15

Language.Go.genBlocks = deriveGen
