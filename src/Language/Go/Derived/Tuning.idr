module Language.Go.Derived.Tuning

import Language.Go.Model

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
GenOrderTuning "AnonFunc".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{pb}]

export
GenOrderTuning "DeclareVar".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{newName}, `{na}, `{ty}, `{initial}]
