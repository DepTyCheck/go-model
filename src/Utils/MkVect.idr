module Utils.MkVect

import Decidable.Equality

import Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops


export
mkListType : Elaboration m => (of_ : TTImp) -> (name : String) -> m ()
mkListType of_ name = do
  let newType = varStr name
  let ns = MkNS [name]
  let cons = var $ NS ns `{(::)}
  declare $ [ INamespace emptyFC ns $
    [ simpleData Public (fromString name)
      [ mkTy "Nil" newType
      , mkTy "::" $ arg of_ .-> arg newType .-> newType
      ]

    , public' `{asList} `(~newType -> List ~of_)
    , def `{asList}
      [ `(asList Nil) .= `(Nil)
      , `(asList (x :: xs)) .= `(x :: asList xs)
      ]

    , public' `{length} `(~newType -> Nat)
    , def `{length}
      [ `(length xs) .= `(length $ asList xs)
      ]

    , interfaceHint Public `{biinjectiveHint} `(Biinjective ~cons)
    , def `{biinjectiveHint}
      [ `(biinjectiveHint) .= `(MkBiinjective $ \case Refl => (Refl, Refl))
      ]
    ]
  ]


export
deriveDecEq : Elaboration m => (name : String) -> m ()
deriveDecEq name = do
  let decEqImpl: Name = fromString $ "decEq" ++ name
  let listType = var $ fromString name
  let ns = MkNS [name]
  declare
    [ export' decEqImpl
      `((x1 : ~listType) -> (x2 : ~listType) -> Dec (x1 = x2))
    , interfaceHint Public `{decEqHint} `(DecEq ~listType)
    , def decEqImpl
      [ `(~(var decEqImpl) Nil Nil) .= `(Yes Refl)
      , `(~(var decEqImpl) (x :: xs) Nil) .= `(No $ \case Refl impossible)
      , `(~(var decEqImpl) Nil (x' :: xs')) .= `(No $ \case Refl impossible)
      , `(~(var decEqImpl) (x :: xs) (x' :: xs')) .=
        `(assert_total decEqCong2 (decEq x x') (decEq xs xs'))
      ]
    , def `{decEqHint}
      [ `(decEqHint) .= `(mkDecEq ~(var decEqImpl))
      ]
    ]

