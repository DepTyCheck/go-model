module Language.Go.Aux

import Data.DPair

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


namespace Declaration
  export
  asList : Block -> List Declaration
  asList [] = []
  asList (d :: ds) = d :: asList ds


namespace Expr
  export
  asList : forall ctxt, rets.
           (ExprList ctxt rets) ->
           List (Exists $ Expr ctxt)
  asList {rets=[]} [] = []
  asList {rets=(t :: ts)} (e :: es) = (Evidence [t] e) :: asList es

namespace Statement
  export
  isEmpty : forall ctxt. Statement ctxt -> Bool
  isEmpty JustStop = True
  isEmpty _ = False
