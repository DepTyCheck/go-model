module Language.Go.Aux

import Language.Go.Model


export
defaultBlocks : BlockStack
defaultBlocks = MkBlockStack [] Nothing

export
defaultContext : Context
defaultContext = MkContext
  { blocks = defaultBlocks
  , returns = [GoInt]
  , isTerminating = True
  }

