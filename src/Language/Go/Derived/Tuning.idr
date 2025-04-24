module Language.Go.Derived.Tuning

import Language.Go.Model

import Deriving.DepTyCheck.Gen

export
GenOrderTuning "Var'".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{initial}]

export
GenOrderTuning "ApplyPrefix".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{op}]

export
GenOrderTuning "CallBuiltin".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{func}]
