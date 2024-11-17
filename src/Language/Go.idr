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
      args: SnocListTy
      rets: SnocListTy

    public export
    data Ty
      = NoValue
      | Int'
      | Bool'
      | Func' FuncTy

    public export
    data SnocListTy : Type where
      Lin  : SnocListTy
      (:<) : SnocListTy -> Ty -> SnocListTy

  mutual
    public export
    Eq FuncTy where
      (==) (MkFuncTy a c) (MkFuncTy a' c') = a == a' && c == c'

    %runElab derive "Ty" [DE.Eq]

    public export
    Eq SnocListTy where
      (==) Lin Lin = True
      (==) (xs :< x) (xs' :< x') = assert_total $ xs == xs' && x == x'
      (==) _ _ = False

  public export
  snocListTyToList : SnocListTy -> List Ty
  snocListTyToList Lin = []
  snocListTyToList (xs :< x) = (snocListTyToList xs) ++ [x]

  public export
  length : SnocListTy -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export %inline
  (.length) : SnocListTy -> Nat
  (.length) = length

  export
  Biinjective Ty.MkFuncTy where
    biinjective Refl = (Refl, Refl)

  export
  Biinjective Ty.(:<) where
    biinjective Refl = (Refl, Refl)

  mutual
    export
    DecEq FuncTy where
      decEq (MkFuncTy a c) (MkFuncTy a' c') = decEqCong2 (decEq a a') (decEq c c')

    %runElab derive "Ty" [Generic, DecEq]

    export
    DecEq SnocListTy where
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
  data Expr : Context -> Ty -> Type where
    C : (x : Literal ty) -> Expr ctxt ty

  export
  Show (Expr ctxt ty) where
    show (C val) = "(C " ++ show val ++ ")"

namespace Stmt

  public export
  data Statement : (ctxt : Context) -> (contTy : Ty) -> Type where
    Nop : Statement ctxt contTy

    Ret : (res : Expr ctxt contTy) -> Statement ctxt contTy

  export
  Show (Statement ctxt contTy) where
    show Nop = "Nop"
    show (Ret res) = "(Ret " ++ show res ++ ")"

export
genStmts : Fuel -> (ctxt : Context) -> (contTy : Ty) -> Gen MaybeEmpty $ Statement ctxt contTy
