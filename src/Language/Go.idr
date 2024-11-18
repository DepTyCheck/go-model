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
  data SnocListDef : Type where
    Lin  : SnocListDef
    (:<) : SnocListDef -> Def -> SnocListDef

  public export
  Context : Type
  Context = SnocListDef

namespace Expr

  public export
  data Literal : Ty -> Type where
    MkInt : Nat -> Literal Int'
    MkBool : Bool -> Literal Bool'

  export
  Show (Literal ty) where
    show (MkInt x) = show x
    show (MkBool x) = show x

  public export
  data Expr : (ctxt : Context) -> (res : Types) -> Type where
    C : (x : Literal ty) -> Expr ctxt [<ty]

  export
  Show (Expr ctxt res) where
    show (C val) = "(C " ++ show val ++ ")"

namespace Stmt
  public export
  data Statement : (ctxt : Context) ->
                   (cont : Types) ->
                   (mustTerm : Bool) ->
                   Type where
    End : Statement ctxt cont False

    Ret : (res : Expr ctxt cont) -> Statement ctxt cont mustTerm

  export
  Show (Statement ctxt cont opts) where
    show End = "End"
    show (Ret res) = "(Ret " ++ show res ++ ")"

export
genStmts : Fuel -> (ctxt : Context) -> (cont : Types) -> (mustTerm : Bool) ->
                   Gen MaybeEmpty $ Statement ctxt cont mustTerm
