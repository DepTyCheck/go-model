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
GenOrderTuning "ChanOp.Send".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{chan}]

export
GenOrderTuning "Call.MkCall".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{s}]

export
ProbabilityTuning `{Block.Term}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{Stmt.SReturn}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{Stmt.SVar1}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{Stmt.SCall}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{Stmt.SChanOp}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 6

-- @WHEN IF_STMTS
export
ProbabilityTuning `{Stmt.SIf}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1
-- @END IF_STMTS

-- export
-- ProbabilityTuning `{Stmt.SLoop}.dataCon where
--   isConstructor = itIsConstructor
--   tuneWeight = const 1

export
ProbabilityTuning `{ChanOp.Open}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 1

export
ProbabilityTuning `{ChanOp.Send}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 16

export
ProbabilityTuning `{ChanOp.Recv}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 16
