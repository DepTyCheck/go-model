module Language.Go.Derived.Tuning

import Language.Go.Model

import Deriving.DepTyCheck.Gen

export
GenOrderTuning "SVar1".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{initial}]

export
GenOrderTuning "EUnary".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{func}]

export
GenOrderTuning "EBinary".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{func}]
