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
  let stack :=
        [< MkDecl Var $ GS GInt
         , MkDecl Var $ funcTy [GInt] Nothing
         , MkDecl Var $ funcTy [GInt, GBool] (Just GInt)
        ]
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
      , isTerminating = True
      }


-- dip'' : forall len.
--         (depth   : Nat) ->
--         (0 bound : LT depth len) =>
--         (st      : Stack len) ->
--         (Exists Decl)
-- dip'' 0 (_ :< decl) =
--   Evidence _ decl
-- dip'' {len = S restLen} (S i) @{bound} (rest :< decl) =
--   let 0 lt' : (LT i restLen) = fromLteSucc bound
--    in dip'' i rest
-- dip'' i @{bound} [<] = void (absurd bound)


export
dip :  forall len.
     (depth : Fin len) ->
     (stack : Stack len) ->
     (Stack (finToNat $ complement depth), Decl)
dip {len = S top} FZ (rest :< decl) =
  rewrite finToNatLastIsBound {n = top} in (rest, decl)
dip {len = S top} (FS d) (rest :< _) =
  rewrite finToNatWeakenNeutral {n = complement {n = top} d}
       in dip d rest


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


public export
record ResolvedDecl where
  constructor MkDecl
  kind : Kind
  name : Nat
  type : GType


export
resolve : {len : Nat} ->
          (depth : Fin len) ->
          (stack : Stack len) ->
          ResolvedDecl
resolve depth stack =
  let name := finToNat $ complement depth
      decl := snd $ dip depth stack
   in MkDecl
        { kind = decl.kind
        , name = name
        , type = decl.type
        }


takeTopRev : {len : Nat} ->
             (count : Nat) ->
             (stack : Stack len) ->
             List ResolvedDecl
takeTopRev Z _ = []
takeTopRev _ [<] = []
takeTopRev (S i) stack@(rest :< _) =
  resolve 0 stack :: takeTopRev i rest

export
takeTopDecl : {len : Nat} ->
              (count : Nat) ->
              (stack : Stack len) ->
              List ResolvedDecl
takeTopDecl count stack = reverse $ takeTopRev count stack


namespace ExprList
  export
  asList : forall ctxt, len.
           {types : TypeVect len} ->
           ExprList ctxt types ->
           List (type : Scalar ** Expr ctxt (GS type))
  asList [] = []
  asList {types = t :: ts} (e :: es) =
    (t ** e) :: asList es


namespace Statement
  export
  isEmpty : forall ctxt. Statement ctxt -> Bool
  isEmpty SStop = True
  isEmpty _ = False

  public export
  context : {ctxt : Context} -> (0 _ : Statement ctxt) -> Context
  context {ctxt} _ = ctxt

  public export
  contextSpec : forall ctxt.
                (0 stmt : Statement ctxt) ->
                (context stmt = ctxt)
  contextSpec _ = Refl
