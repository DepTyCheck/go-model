module Language.Go.Derived.Tuning

import Language.Go

import Deriving.DepTyCheck.Gen

-- @WHEN EXTRA_BUILTINS
-- @ export
-- @ GenOrderTuning "ApplyPrefix".dataCon where
  -- @ isConstructor = itIsConstructor
  -- @ deriveFirst _ _ = [`{op}]
-- @END EXTRA_BUILTINS

export
GenOrderTuning "ApplyInfix".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{op}]

export
GenOrderTuning "DeclareVar".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{ty}, `{newName}, `{d}, `{initial}]
