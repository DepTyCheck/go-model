module Language.Go.Derived.Tuning

import Language.Go.Model

import Deriving.DepTyCheck.Gen

export
GenOrderTuning "SVar1".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{initial}]

-- @WHEN EXTRA_BUILTINS
-- @ export
-- @ GenOrderTuning "ApplyPrefix".dataCon where
-- @   isConstructor = itIsConstructor
-- @   deriveFirst _ _ = [`{op}]
-- @END EXTRA_BUILTINS
