module Language.Go.Aux

import Data.DPair
import Data.Fin
import Data.Fin.Properties
import Data.List

import Language.Go.Model

%unbound_implicits off


public export
funcTy : {parLen : Nat} ->
         (parTypes : TypeVect parLen) ->
         (retType : MaybeType) ->
         GType
funcTy par ret = GFunc $ par `To` ret

-- enumerate : forall t. {default 0 start : Nat} -> List t -> List (Nat, t)
-- enumerate Nil = Nil
-- enumerate {start} (x :: xs) =
--   (start, x) :: enumerate {start = S start} xs


namespace TypeVect
  export
  asList : forall len. TypeVect len -> List Scalar
  asList [] = []
  asList (t :: ts) = t :: asList ts


public export
defaultStack : (len : Nat ** Stack len)
defaultStack =
  let stack := [<]
        -- [< MkDecl Var $ GS GInt
        --  , MkDecl Var $ funcTy [GInt] Nothing
        --  , MkDecl Var $ funcTy [GInt, GBool] (Just GInt)
        -- ]
   in (_ ** stack)

public export
defaultContext : Context
defaultContext =
  let (stackDepth ** stack) := defaultStack in
    MkContext
      { stackLen      = stackDepth
      , stack         = stack
      , blockDepth    = last
      , returns       = Just GInt
      }


export
byElemToByType : forall elem, stack, idx.
                 ByElem elem stack idx ->
                 ByType (GChan elem) stack idx
byElemToByType HereE = HereT
byElemToByType (ThereE there) = ThereT (byElemToByType there)


export
dip : forall len.
      (depth : Fin len) ->
      (stack : Stack len) ->
      (Stack (finToNat $ complement depth), Decl)
dip {len = S top} FZ (rest :< decl) =
  rewrite finToNatLastIsBound {n = top} in (rest, decl)
dip {len = S top} (FS d) (rest :< _) =
  rewrite finToNatWeakenNeutral {n = complement {n = top} d}
       in dip d rest


export
get : forall len. (depth : Fin len) -> (stack : Stack len) -> Decl
get depth stack = snd $ dip depth stack


-- public export
-- index
--   :  {len    : Nat}
--   -> (i      : Fin len)
--   -> (stack  : Stack len)
--   -> (Stack (finToNat i), Decl (finToNat i))
-- index {len} i stack =
--   let depth : Fin len
--       depth = complement i
--    in rewrite sym (complementInvolutive i) in dip depth stack


takeTopRev : {len : Nat} ->
             (count : Nat) ->
             (stack : Stack len) ->
             List Decl
takeTopRev Z _ = []
takeTopRev _ [<] = []
takeTopRev (S i) stack@(rest :< top) =
  top :: takeTopRev i rest

export
takeTopDecl : {len : Nat} ->
              (count : Nat) ->
              (stack : Stack len) ->
              List Decl
takeTopDecl count stack = reverse $ takeTopRev count stack


namespace ExprList
  export
  traverse : forall m, b, len.
             {cnt : _} -> {ctxt : _} -> {types : TypeVect len} ->
             Applicative m =>
             ({cnt' : Nat} -> {type : GType} -> Expr cnt' ctxt type -> m b) ->
             ExprList cnt ctxt types ->
             m (List b)
  traverse f [] = pure []
  traverse f (e :: es) = [| f e :: traverse f es |]


namespace ExprHList
  export
  traverse : forall m, b.
             {cnt : _} -> {ctxt : _} -> {type : _} ->
             Applicative m =>
             ({cnt' : Nat} -> Expr cnt' ctxt type -> m b) ->
             ExprHList cnt ctxt type ->
             m (List b)
  traverse f [] = pure []
  traverse f (e :: es) = [| f e :: traverse f es |]



export
onChanOpReturns : forall cnt, ctxt.
                  (op : ChanOp cnt ctxt) ->
                  (ctxt.returns = (chanOpCtxt op).returns)
onChanOpReturns {ctxt = MkContext {}} (Open _ _) = Refl
onChanOpReturns (Send _ _) = Refl
onChanOpReturns {ctxt = MkContext {}} (Recv _) = Refl


namespace Block
  export
  isEmpty : forall cnt, ctxt, isTerm. Block cnt ctxt isTerm -> Bool
  isEmpty End = True
  isEmpty _ = False

  export
  stmtCtxtReturns : forall cnt, ctxt, isTerm.
                    (stmt : Stmt cnt ctxt isTerm) ->
                    (ctxt.returns = (stmtCtxt stmt).returns)
  stmtCtxtReturns {ctxt = MkContext {}} (SVar1 {newType} _) = Refl
  stmtCtxtReturns (SChanOp op) = onChanOpReturns op
  stmtCtxtReturns (SReturn res) = Refl
  stmtCtxtReturns (SCall async call) = Refl
  stmtCtxtReturns (SIf test then_ else_) = Refl
  stmtCtxtReturns (SLoop type elems body) = Refl

