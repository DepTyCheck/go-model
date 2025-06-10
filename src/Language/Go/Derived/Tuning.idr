module Language.Go.Derived.Tuning

import Language.Go.Model

import Deriving.DepTyCheck.Gen

export
GenOrderTuning "SVar1".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{initial}]

-- export
-- GenOrderTuning "EUnary".dataCon where
--   isConstructor = itIsConstructor
--   deriveFirst _ _ = [`{func}]

-- export
-- GenOrderTuning "EBinary".dataCon where
--   isConstructor = itIsConstructor
--   deriveFirst _ _ = [`{func}]

export
ProbabilityTuning `{Block.Term}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{SReturn}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{SVar1}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{SCall}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{SChanOp}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 6

-- @WHEN IF_STMTS
export
ProbabilityTuning `{SIf}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1
-- @END IF_STMTS

-- export
-- ProbabilityTuning `{SLoop}.dataCon where
--   isConstructor = itIsConstructor
--   tuneWeight = const 1

export
ProbabilityTuning `{Model.Open}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{Model.Send}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 16

export
ProbabilityTuning `{Model.Recv}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 16
