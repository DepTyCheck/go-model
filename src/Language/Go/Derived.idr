module Language.Go.Derived

import public Language.Go.Model
import public Language.Go.Derived.Tuning

import Data.Fin.Properties
import Data.Nat.Order.Properties

import Deriving.DepTyCheck.Gen

import Syntax.PreorderReasoning

%default total

%unbound_implicits off
%logging "deptycheck.derive" 15


Language.Go.Model.genStmts = deriveGen

-- %language ElabReflection

-- %runElab deriveGenPrinter {printTTImp = False} $
--   Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Statement ctxt

