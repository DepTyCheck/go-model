module Language.Go.Derived.Tuning

import Language.Go.Model

import Deriving.DepTyCheck.Gen

export
GenOrderTuning "Var'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{initial}]
