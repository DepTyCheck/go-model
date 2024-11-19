module Language.Go

import Data.Fuel
import Data.Nat
import Data.SOP

import Decidable.Equality

import Derive.Eq as DE

import Generics.Derive

import Test.DepTyCheck.Gen

import Utils.MkSnocList

%language ElabReflection

namespace Ty
  mutual
    public export
    record FuncTy where
      constructor MkFuncTy
      args: Types
      rets: Types

    public export
    data Ty
      = Int'
      | Bool'
      | Func' FuncTy

    public export
    data MaybeTy
      = Nothing
      | Just Ty

    public export
    data Types : Type where
      Lin  : Types
      (:<) : Types -> Ty -> Types

  mutual
    %runElab derive "FuncTy" [DE.Eq]
    %runElab derive "Ty" [DE.Eq]
    %runElab derive "MaybeTy" [DE.Eq]

    public export
    Eq Types where
      (==) Lin Lin = True
      (==) (xs :< x) (xs' :< x') = assert_total $ xs == xs' && x == x'
      (==) _ _ = False

  public export
  snocListTyToList : Types -> List Ty
  snocListTyToList Lin = []
  snocListTyToList (xs :< x) = (snocListTyToList xs) ++ [x]

  public export
  length : Types -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : Types -> Nat
  (.length) = length

  export
  Biinjective Ty.MkFuncTy where
    biinjective Refl = (Refl, Refl)

  export
  Biinjective Ty.(:<) where
    biinjective Refl = (Refl, Refl)

  mutual
    %runElab derive "FuncTy" [Generic, DecEq]
    %runElab derive "Ty" [Generic, DecEq]
    %runElab derive "MaybeTy" [Generic, DecEq]

    export
    DecEq Types where
      decEq Lin Lin = Yes Refl
      decEq Lin (_ :< _) = No $ \case Refl impossible
      decEq (_ :< _) Lin = No $ \case Refl impossible
      decEq (xs :< x) (xs' :< x') = decEqCong2 (decEq xs xs') (decEq x x')


namespace Def
  public export
  data Def : Type where
    DVar : (varTy : Ty) -> Def

  public export
  data Context : Type where
    Lin  : Context
    (:<) : Context -> Def -> Context

  public export
  data IndexIn : Context -> Type where
    Here  : IndexIn $ sx :< x
    There : IndexIn sx -> IndexIn $ sx :< x

  public export
  index : (sx : Context) -> IndexIn sx -> Def
  index (_ :<x) Here      = x
  index (sx:<_) (There i) = index sx i

  public export
  length : Context -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : Context -> Nat
  (.length) = length

  public export
  data AtIndex : {sx : Context} -> (idx : IndexIn sx) -> Def -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = sx :< sig} Here sig
    There' : AtIndex {sx} i sig -> AtIndex {sx = sx :< x} (There i) sig

namespace Expr

  public export
  data Literal : Ty -> Type where
    MkInt : Nat -> Literal Int'
    MkBool : Bool -> Literal Bool'

  export
  Show (Literal ty) where
    show (MkInt x) = show x
    show (MkBool True) = "true"
    show (MkBool False) = "false"

  public export
  data Expr : (ctxt : Context) -> (res : Types) -> Type where
    Const : (x : Literal ty) -> Expr ctxt [<ty]

namespace Block
  ||| Weater the current block is the last one in the current function
  public export
  data PosInFunc
    = Intermediate
    | Terminating

  mutual
    public export
    data InterStmt : (ctxt : Context) ->
                     (ret : Types) ->
                     (pos : PosInFunc) ->
                     Type where
      -- ExprStmt : {res : Types} -> (expr : Expr ctxt res) -> InterStmt ctxt ret pos

      InterIf : (test : Expr ctxt [<Bool']) ->
           (th, el : Block ctxt ret Intermediate)->
           InterStmt ctxt ret pos

    public export
    data LastStmt : (ctxt : Context) ->
                    (ret : Types) ->
                    (pos : PosInFunc) ->
                    Type where
      JustStopI : LastStmt ctxt ret Intermediate

      JustStopN : LastStmt ctxt [<] pos

      Ret : (res : Expr ctxt ret) -> LastStmt ctxt ret pos

      LastIf : (test : Expr ctxt [<Bool']) ->
               (th, el : Block ctxt ret pos)->
               LastStmt ctxt ret pos

    -- public export
    -- data AnyStmt : (ctxt : Context) ->
    --                (ret : Types) ->
    --                (pos : PosInFunc) ->
    --                Type where

    public export
    data Block : (ctxt : Context) ->
                 (ret : Types) ->
                 (pos : PosInFunc) ->
                 Type where
      ContI : InterStmt ctxt ret pos ->
              Block ctxt ret pos ->
              Block ctxt ret pos

      -- ContA : AnyStmt ctxt ret pos ->
      --         Block ctxt ret pos ->
      --         Block ctxt ret pos

      LastL : LastStmt ctxt ret pos -> Block ctxt ret pos

      -- LastA : AnyStmt ctxt ret pos -> Block ctxt ret pos

  export
  isEmpty : Block _ _ _ -> Bool
  isEmpty (LastL JustStopI) = True
  isEmpty (LastL JustStopN) = True
  isEmpty _ = False

export
genBlocks : Fuel -> (ctxt : Context) -> (ret : Types) -> (pos : PosInFunc) ->
                   Gen MaybeEmpty $ Block ctxt ret pos
