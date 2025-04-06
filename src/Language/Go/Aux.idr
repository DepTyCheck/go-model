module Language.Go.Aux

import Data.DPair
import Data.Fin
import Data.Fin.Properties
import Data.Nat.Order.Properties
import Data.List
import Data.Maybe
import Data.So
import Data.Zippable

import Decidable.Equality  -- remove later


import Language.Go.Model


%unbound_implicits off


namespace GoType
  export
  asList : forall len. TypeVect len -> List GoType
  asList [] = []
  asList (t :: ts) = t :: asList ts

  public export
  funcTy : {n_par, n_ret : Nat} ->
           (params : TypeVect n_par) ->
           (returns : TypeVect n_ret) ->
           GoType
  funcTy params returns = GoFunc $ MkGoFuncType params returns


  data GoTypeView : GoType -> Type where
    GoFunc' : {n_par, n_ret : Nat} ->
              (par : TypeVect n_par) ->
              (ret : TypeVect n_ret) ->
              GoTypeView (GoFunc $ MkGoFuncType par ret)
    Scalar : forall t. GoTypeView t

  view : (it : GoType) -> GoTypeView it
  view (GoFunc $ MkGoFuncType par ret) = GoFunc' par ret
  view _ = Scalar

  export
  isFunc : GoType -> Bool
  isFunc t with (view t)
    isFunc _ | GoFunc' par ret = True
    isFunc _ | Scalar = False


[Test] DecEq GoFuncType where
  decEq (MkGoFuncType {n_par = np1} {n_ret = nr1} p1 r1)
        (MkGoFuncType {n_par = np2} {n_ret = nr2} p2 r2) =
          let Yes Refl = decEq np1 np2
            | No contra => No $ \eq => contra $ fst $ injMk eq
            ; Yes Refl = decEq nr1 nr2
            | No contra => No $ \eq => contra $ fst $ snd $ injMk eq
            ; Yes eqPar = decEq p1 p2
            | No contra => No $ \eq => contra $ fst $ snd $ snd $ injMk eq
            ; Yes eqRet = decEq r1 r2
            | No contra => No $ \eq => contra $ snd $ snd $ snd $ injMk eq
          in
            Yes $ congMk eqPar eqRet
    where
      congMk : forall n_par, n_ret.
               {0 p1, p2 : TypeVect n_par} ->
               {0 r1, r2 : TypeVect n_ret} ->
               (0 _ : p1 = p2) ->
               (0 _ : r1 = r2) ->
               (MkGoFuncType p1 r1 = MkGoFuncType p2 r2)
      congMk Refl Refl = Refl

      injMk : forall n_par1, n_par2, n_ret1, n_ret2.
              {0 p1 : TypeVect n_par1} ->
              {0 p2 : TypeVect n_par2} ->
              {0 r1 : TypeVect n_ret1} ->
              {0 r2 : TypeVect n_ret2} ->
              (0 _  : MkGoFuncType p1 r1 = MkGoFuncType p2 r2) ->
              (n_par1 = n_par2, n_ret1 = n_ret2, p1 = p2, r1 = r2)
      injMk Refl = (Refl, Refl, Refl, Refl)


-- TODO: можно ли удобно работать с implicit аргументами?

-- TODO: is it slow?
-- public export
-- weaken : Fin n -> Fin (S n)
-- weaken FZ     = FZ
-- weaken (FS k) = FS $ weaken k

-- => ThereT is O(n^2) ????

export
enumerate : forall t. {default 0 start : Nat} -> List t -> List (Nat, t)
enumerate Nil = Nil
enumerate {start} (x :: xs) = (start, x) :: enumerate {start = S start} xs


export
defaultStack : (len : Nat ** Stack len)
defaultStack =
  let stack =
    [< MkDecl Var GoInt UniqueName
     , MkDecl Var ([GoInt, GoInt] `funcTy` [GoBool]) UniqueName
    ]
  in (_ ** stack)

export
defaultContext : Context
defaultContext =
  let (stackDepth ** stack) = defaultStack in
    MkContext
    { stackLen = stackDepth
    , stack = stack
    , blockStart = 0
    , returnsLen = 1
    , returns = [GoBool]
    , isTerminating = True
    }


namespace Stack
  dip'' : forall len.
          (depth   : Nat) ->
          (0 bound : LT depth len) =>
          (st      : Stack len) ->
          (Exists Decl)
  dip'' 0 (_ :< decl) =
    Evidence _ decl
  dip'' {len = S restLen} (S i) @{bound} (rest :< decl) =
    let 0 lt' : (LT i restLen) = fromLteSucc bound
     in dip'' i rest
  dip'' i @{bound} [<] = void (absurd bound)


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
          (st : Stack len) ->
          (Stack (finToNat i), Decl (finToNat i))
  index {len} i st =
    let depth : Fin len
      ; depth = complement i
    in rewrite sym (complementInvolutive i) in
      dip depth st


  public export
  record ResolvedDecl where
    constructor MkDecl
    kind : Kind
    type : GoType
    name : Nat


  export
  resolve : {len : Nat} ->
            (idx : Fin len) ->
            (st  : Stack len) ->
            ResolvedDecl
  resolve idx st =
    let pair@(rest, decl) = index idx st in
      MkDecl
        { kind = decl.kind
        , type = decl.type
        , name = resolveName pair
        }

    where
      resolveName : {i : Nat} -> (Stack i, Decl i) -> Nat
      resolveName {i} (rest, decl) =
        case decl.shadows of
             UniqueName => i
             Shadows next => assert_total resolveName (index next rest)



namespace Expr
  export
  asList : forall ctxt, len.
           {0 rets : TypeVect len} ->
           (ExprList ctxt rets) ->
           List (Exists $ Expr ctxt {len = 1})
  asList {rets=[]} [] = []
  asList {rets=(t :: ts)} (e :: es) =
    (Evidence [t] e) :: asList es

namespace Statement
  export
  isEmpty : forall ctxt. Statement ctxt -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

