module Language.Go.Aux

import Data.DPair
import Data.Maybe
import Data.So

import Language.Go.Model


export
extendBlock : Declaration -> Block -> Maybe Block
extendBlock decl blk =
  case choose $ isNameAbsent blk decl.name of
     Left _ => Just $ decl :: blk
     Right _ => Nothing


export
defaultBlock : Block
defaultBlock =
  let name = MkName 42 in
  let _ = Wrap Oh in
  [Declare Var name (GoFunc [GoInt, GoInt] [GoBool])]

export
defaultBlocks : BlockStack
defaultBlocks = MkBlockStack defaultBlock Nothing

export
defaultContext : Context
defaultContext = MkContext
  { blocks = defaultBlocks
  , returns = [GoBool]
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
