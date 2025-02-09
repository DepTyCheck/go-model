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
    data Ty
      = Int'
      | Bool'
      | Func' Types Types

    public export
    data Types : Type where
      Lin  : Types
      (:<) : Types -> Ty -> Types

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
  Biinjective Ty.(:<) where
    biinjective Refl = (Refl, Refl)

  export
  Biinjective Ty.Func' where
    biinjective Refl = (Refl, Refl)

  mutual
    export
    DecEq Ty where
      decEq Int' Int' = Yes Refl
      decEq Bool' Bool' = Yes Refl
      decEq (Func' t1 r1) (Func' t2 r2) = decEqCong2 (assert_total decEq t1 t2) (assert_total decEq r1 r2)
      decEq Int' Bool' = No $ \case Refl impossible
      decEq Int' (Func' _ _) = No $ \case Refl impossible
      decEq Bool' Int' = No $ \case Refl impossible
      decEq Bool' (Func' _ _) = No $ \case Refl impossible
      decEq (Func' _ _) Int' = No $ \case Refl impossible
      decEq (Func' _ _) Bool' = No $ \case Refl impossible

    export
    DecEq Types where
      decEq Lin Lin = Yes Refl
      decEq Lin (_ :< _) = No $ \case Refl impossible
      decEq (_ :< _) Lin = No $ \case Refl impossible
      decEq (xs :< x) (xs' :< x') = decEqCong2 (decEq xs xs') (decEq x x')


namespace Definition
  public export
  data Kind
    = Var
    | Const
    | Func

  public export
  record Definition where
    constructor Define
    kind  : Kind
    defTy : Ty
    name  : Nat

  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Definition" [Generic, DecEq]

  export
  Show Definition where
    show (Define Var _ name) = "v" ++ show name
    show (Define Const _ name) = "c" ++ show name
    show (Define Func _ name) = "f" ++ show name

  public export
  data Definitions : Type where
    Lin  : Definitions
    (:<) : Definitions -> Definition -> Definitions

  public export
  data Depth : Definitions -> Type where
    Z : Depth $ sx :< x
    S : Depth sx -> Depth $ sx :< x

  public export
  data AtDepth : (defs : Definitions) ->
                 (idx : Depth defs) ->
                 (dfn : Definition) ->
                 Type where
    Here  : AtDepth (_ :< dfn) Z dfn
    There : AtDepth rest idx dfn ->
            AtDepth (rest :< _) (S idx) dfn

  export
  dig : (defs : Definitions) -> (idx: Depth defs) -> Definition
  dig (_ :< x) Z = x
  dig (sx :< _) (S i) = dig sx i

  public export
  data DefTypeIs : (defs : Definitions) ->
                   (idx : Depth defs) ->
                   (ty : Ty) ->
                   Type where
    -- Is : AtDepth defs idx (Define _ ty _) ->
    --      DefTypeIs defs idx ty
    Here'  : DefTypeIs (_ :< (Define _ ty _)) Z ty
    There' : DefTypeIs rest idx ty ->
             DefTypeIs (rest :< _) (S idx) ty



namespace Expr
  public export
  data Expr : (defs : Definitions) -> (res : Types) -> Type where
    IntLiteral  : (x : Nat) -> Expr defs [<Int']
    BoolLiteral : (x : Bool) -> Expr defs [<Bool']
    GetVar : (idx : Depth defs) ->
             DefTypeIs defs idx ty =>
             Expr defs [<ty]


namespace Block
  public export
  data AllowJustStop : (rets : Types) ->
                       (isTerminating : Bool) ->
                       Type where
    StopWhenNonTerminating : AllowJustStop _ False
    StopWhenReturnNone : AllowJustStop [<] isTerminating


  public export
  data AllowInnerIf : (isTerminatingThen : Bool) ->
                      (isTerminatingElse : Bool) ->
                      Type where
    InnerIfCC : AllowInnerIf False False
    InnerIfCT : AllowInnerIf False True
    InnerIfTC : AllowInnerIf True False


  mutual
    public export
    data Block : (defs : Definitions) ->
                 (rets : Types) ->
                 (ser : Nat) ->
                 (isReturning : Bool) ->
                 Type where

      JustStop : AllowJustStop rets isTerminating =>
                 Block defs rets ser isTerminating

      Return : (res : Expr defs rets) ->
               Block defs rets ser True

      InnerIf : (test : Expr defs [<Bool']) ->
                AllowInnerIf isTerminatingThen isTerminatingElse =>
                (th : Block defs rets ser isTerminatingThen) ->
                (el : Block defs rets ser isTerminatingElse) ->
                (cont : Block defs rets ser isTerminating) ->
                Block defs rets ser isTerminating

      TermIf : (test : Expr defs [<Bool']) ->
               (th : Block defs rets ser True) ->
               (el : Block defs rets ser True) ->
               Block defs rets ser True

      InitVar : (newTy : Ty) ->
                (initVal : Expr oldDefs [<newTy]) ->
                {ser : Nat} ->
                (cont : Block (oldDefs :< Define Var newTy ser) rets (S ser) isTerminating) ->
                Block oldDefs rets ser isTerminating

  export
  isEmpty : Block _ _ _ _ -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genBlocks : Fuel -> (defs : Definitions) -> (rets : Types) -> (ser : Nat) -> (isTerminating : Bool) ->
            Gen MaybeEmpty $ Block defs rets ser isTerminating
