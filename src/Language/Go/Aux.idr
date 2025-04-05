module Language.Go.Aux

import Data.DPair
import Data.Fin
import Data.Fin.Properties
import Data.Nat.Order.Properties
import Data.List
import Data.Maybe
import Data.So
import Data.Zippable

import Language.Go.Model


%unbound_implicits off


export
enumerate : forall t. {default 0 start : Nat} -> List t -> List (Nat, t)
enumerate Nil = Nil
enumerate {start} (x :: xs) = (start, x) :: enumerate {start = S start} xs


export
defaultStack : (len : Nat ** Stack len)
defaultStack =
  let stack =
    [< MkDecl Var GoInt Nothing
     , MkDecl Var (GoFunc [GoInt, GoInt] [GoBool]) Nothing
    ]
  in (_ ** stack)

export
defaultContext : Context
defaultContext =
  let (stackDepth ** stack) = defaultStack in
    MkContext
    { stackLen = stackDepth
    , stack = stack
    , currentBlock = 0
    , returns = [GoBool]
    , isTerminating = True
    }


namespace Stack
  public export
  dip : forall len.
         (depth : Fin len) ->
         Stack len ->
         let idx = finToNat $ complement depth in
         (Stack idx, Decl idx)
  dip {len = S top} FZ (rest :< decl) =
    rewrite finToNatLastIsBound {n = top} in (rest, decl)
  dip {len = S top} (FS d) (rest :< _) =
    rewrite finToNatWeakenNeutral {n = complement {n = top} d} in
            dip d rest


  public export
  index : {len : Nat} ->
         (i : Fin len) ->
         Stack len ->
         (Stack (finToNat i), Decl (finToNat i))
  index {len} i st =
    let depth : Fin len
      ; depth = complement i
    in rewrite sym (complementInvolutive i) in
      dip depth st


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

