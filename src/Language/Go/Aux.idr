module Language.Go.Aux

import Data.DPair
import Data.Fin
import Data.List
import Data.Maybe
import Data.So
import Data.Zippable

import Language.Go.Model


export
enumerate : forall t. {default 0 start : Nat} -> List t -> List (Nat, t)
enumerate Nil = Nil
enumerate {start} (x :: xs) = (start, x) :: enumerate {start = S start} xs


export
defaultStack : (len : Nat ** Stack len)
defaultStack =
  let stack =
    [ Declare Var GoInt
    , Declare Var (GoFunc [GoInt, GoInt] [GoBool])
    ]
  in (_ ** stack)

export
defaultContext : Context
defaultContext =
  let (stackDepth ** stack) = defaultStack in
    MkContext
    { stack = stack
    , stackDepth = stackDepth
    , returns = [GoBool]
    , isTerminating = True
    }


namespace Declaration
  export
  asList : forall len. Stack len -> List Declaration
  asList Nil = Nil
  asList (d :: ds) = d :: asList ds

  -- export
  -- block : forall len.
  --         from : Fin (S len) ->
  --         Stack len ->
  --         List (Fin len, Declaration)
  -- block _ Nil = Nil
  -- block from 
--   export
--   asList : Block -> List Declaration
--   asList [] = []
--   asList (d :: ds) = d :: asList ds


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

  export
  newDecl : forall ctxt.
            {kind : Kind} ->
            DeclareStmt ctxt kind ->
            Declaration
  newDecl stmt = Declare kind stmt.type

  export
  newIndex : forall kind.
             {ctxt : Context} ->
             DeclareStmt ctxt kind ->
             Fin (S ctxt.stackDepth)
  newIndex {ctxt} stmt = last
