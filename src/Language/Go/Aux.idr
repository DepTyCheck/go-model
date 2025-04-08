module Language.Go.Aux

import Data.Fin
import Data.Fin.Properties
import Data.List

import Language.Go.Model

%unbound_implicits off


public export
funcTy
  :  {parLen, retLen : Nat}
  -> (params  : TypeVect parLen)
  -> (returns : TypeVect retLen)
  -> GoType
funcTy params returns =
  GoFunc (MkVectL params) (MkVectL returns)


export
enumerate : forall t. {default 0 start : Nat} -> List t -> List (Nat, t)
enumerate Nil = Nil
enumerate {start} (x :: xs) =
  (start, x) :: enumerate {start = S start} xs


namespace TypeVect
  export
  asList : forall len. TypeVect len -> List GoType
  asList [] = []
  asList (t :: ts) = t :: asList ts

namespace TypeVectL
  %inline
  export
  asList : TypeVectL -> List GoType
  asList (MkVectL vect) = asList vect


export
defaultStack : (len : Nat ** Stack len)
defaultStack =
  let stack :=
        [< MkDecl Var UniqueName GoInt
         , MkDecl Var UniqueName (funcTy [GoInt, GoInt] [GoBool])
        ]
   in (_ ** stack)

export
defaultContext : Context
defaultContext =
  let (stackDepth ** stack) := defaultStack in
    MkContext
      { stackLen      = stackDepth
      , stack         = stack
      , blockDepth    = last
      , returns       = MkVectL [GoBool]
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
dip
  :  forall len
  .  (depth : Fin len)
  -> (stack : Stack len)
  -> let idx := finToNat $ complement depth
      in (Stack idx, Decl idx)
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
  type : GoType


export
resolve
  :  {len : Nat}
  -> (idx : Fin len)
  -> (st  : Stack len)
  -> ResolvedDecl
resolve idx st =
  let pair@(rest, decl) = dip idx st in
    MkDecl
      { kind = decl.kind
      , name = resolveName pair
      , type = decl.type
      }

  where
    resolveName : {i : Nat} -> (Stack i, Decl i) -> Nat
    resolveName {i} (rest, decl) =
      case decl.name of
        UniqueName => i
        Shadows next => assert_total resolveName (dip next rest)


takeTopRev
  :  {len   : Nat}
  -> (count : Nat)
  -> (stack : Stack len)
  -> List ResolvedDecl
takeTopRev Z _ = []
takeTopRev _ [<] = []
takeTopRev (S i) stack@(rest :< _) =
  resolve 0 stack :: takeTopRev i rest

export
takeTopDecl
  :  (count : Nat)
  -> (ctxt  : Context)
  -> List ResolvedDecl
takeTopDecl count ctxt = reverse $ takeTopRev count ctxt.stack

-- TODO
-- export
-- newDeclarations
--   :  {0 ctxt     : Context}
--   -> {count      : Nat}
--   -> {0 kind     : Kind}
--   -> {0 newTypes : TypeVect count}
--   -> {0 newNames : NewNames count ctxt}
--   -> (newCtxt    : Context)
--   -> {auto eq    : (newCtxt =~ OnDeclare ctxt kind newTypes newNames)}
--   -> List ResolvedDecl
-- newDeclarations {eq = Refl} newCtxt =
--   reverse $ takeTopRev count newCtxt.stack


-- namespace Expr
--   export
--   asList : forall ctxt, len.
--            {0 rets : TypeVect len} ->
--            (ExprList ctxt rets) ->
--            List (Exists $ Expr ctxt {len = 1})
--   asList {rets=[]} [] = []
--   asList {rets=(t :: ts)} (e :: es) =
--     (Evidence [t] e) :: asList es

namespace Statement
  export
  isEmpty : forall ctxt. Statement ctxt -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

  public export
  context : {ctxt : Context} -> (0 _ : Statement ctxt) -> Context
  context {ctxt} _ = ctxt

  public export
  contextSpec
    :  {0 ctxt : Context}
    -> (0 stmt : Statement ctxt)
    -> (context stmt = ctxt)
  contextSpec _ = Refl


-- DSL


export
void
  :  {ctxt  : Context}
  -> (expr  : Expr ctxt (MkVectL []))
  -> (cont  : Statement ctxt)
  -> Statement ctxt
void = VoidExpr


public export
(>>)
  :  {ctxt, newCtxt  : Context}
  -> (addCont        : Statement newCtxt -> Statement ctxt)
  -> (cont           : Statement newCtxt)
  -> Statement ctxt
(>>) addCont cont = addCont cont


-- Example

export
example : Statement defaultContext
example =
  VoidExpr (CallBuiltin Print (GetLiteral $ MkInt 42)) $
         (ReturnValue (GetLiteral $ MkBool True))
