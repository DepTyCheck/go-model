module Language.Go.Derived.Tuning

import Language.Go.Model

import Deriving.DepTyCheck.Gen

export
GenOrderTuning "DeclareVar".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{nemp}, `{initial}]
-- export
-- GenOrderTuning "DeclareVar".dataCon where
--   isConstructor = itIsConstructor
--   deriveFirst _ _ = [`{newTypes}]
