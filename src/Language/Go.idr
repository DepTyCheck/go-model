module Language.Go

import Data.Fuel
import Data.Nat
import Data.Fin
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
      Nil  : Types
      (::) : Ty -> Types -> Types

  public export
  length : Types -> Nat
  length Nil = Z
  length (_ :: sx) = S $ length sx

  public export %inline
  (.length) : Types -> Nat
  (.length) = length

  export
  Biinjective Ty.(::) where
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
      decEq Nil Nil = Yes Refl
      decEq Nil (_ :: _) = No $ \case Refl impossible
      decEq (_ :: _) Nil = No $ \case Refl impossible
      decEq (xs :: x) (xs' :: x') = decEqCong2 (decEq xs xs') (decEq x x')


namespace Definition
  public export
  data Kind
    = Var
    | Const
    | Func

  export
  Show Kind where
    show Var = "v"
    show Const = "c"
    show Func = "f"

  public export
  record Definition where
    constructor Define
    defKind  : Kind
    defTy : Ty

  %runElab derive "Kind" [Generic, DecEq]
  %runElab derive "Definition" [Generic, DecEq]

  public export
  data Definitions : (size : Nat) -> Type where
    Nil  : Definitions Z
    (::) : Definition -> Definitions n -> Definitions (S n)

  export
  dig : (defs : Definitions n) -> (idx: Fin n) -> Definition
  dig (x :: _) FZ = x
  dig (_ :: ds) (FS i) = dig ds i

  public export
  data DefTypeIs : (defs : Definitions n) ->
                   (idx : Fin n) ->
                   (ty : Ty) ->
                   Type where
    Here'  : DefTypeIs (Define _ ty :: _) FZ ty
    There' : DefTypeIs rest idx ty ->
             DefTypeIs (_ :: rest) (FS idx) ty


namespace Context
  public export
  data Vars : Type where
    Nil : Vars
    (::) : Nat -> Vars -> Vars

  public export
  record Context where
    constructor MkContext
    depth : Nat
    definitions : Definitions depth
    returns : Types
    shouldReturn : Bool

  public export
  data AddDefinition : (ctxt : Context) ->
                       (kind : Kind) ->
                       (ty : Ty) ->
                       (newCtxt : Context) ->
                       Type where
    MkAddDefinition : AddDefinition ctxt kind ty
                                    (MkContext
                                      (S ctxt.depth)
                                      (Define kind newTy :: ctxt.definitions)
                                      ctxt.returns
                                      ctxt.shouldReturn)

namespace Expr
  public export
  data Expr : (ctxt : Context) -> (res : Types) -> Type where
    IntLiteral  : (x : Nat) -> Expr ctxt [Int']
    BoolLiteral : (x : Bool) -> Expr ctxt [Bool']
    GetVar : (idx : Fin ctxt.depth) ->
             DefTypeIs ctxt.definitions idx ty =>
             Expr ctxt [ty]


namespace Block
  public export
  data AllowJustStop : Context -> Type where
    StopUnlessShouldReturn : AllowJustStop (MkContext _ _ _ False)
    StopWhenReturnNone : AllowJustStop (MkContext _ _ [] _)

  public export
  data AllowReturn : Context -> Types -> Type where
    AllowReturnWhenShould : AllowReturn (MkContext _ _ types True) types

  public export
  data AllowInnerIf : (ctxt, ctxtThen, ctxtElse : Context) ->
                      Type where
    MkAllowInnerIf : AllowInnerIf (MkContext n d r False)
                                  (MkContext n d r _)
                                  (MkContext n d r _)

  public export
  data ShouldReturn : Context -> Type where
    MkShouldReturn : ShouldReturn (MkContext _ _ _ True)

  mutual
    public export
    data Block : (ctxt : Context) -> Type where

      JustStop : AllowJustStop ctxt =>
                 Block ctxt

      Return : AllowReturn ctxt rets =>
               (res : Expr ctxt rets) ->
               Block ctxt

      InnerIf : (test : Expr ctxt [Bool']) ->
                {ctxtThen, ctxtElse : Context} ->
                AllowInnerIf ctxt ctxtThen ctxtElse =>
                (th : Block ctxtThen) ->
                (el : Block ctxtElse) ->
                (cont : Block ctxt) ->
                Block ctxt

      TermIf : ShouldReturn ctxt =>
               (test : Expr ctxt [Bool']) ->
               (th : Block ctxt) ->
               (el : Block ctxt) ->
               Block ctxt

      InitVar : {ctxt, newCtxt : Context} ->
                (newTy : Ty) ->
                (initVal : Expr ctxt [newTy]) ->
                {auto pr : AddDefinition ctxt Var newTy newCtxt} ->
                (cont : Block newCtxt) ->
                Block ctxt

  export
  isEmpty : Block _ -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genBlocks : Fuel -> (ctxt : Context) -> Gen MaybeEmpty $ Block ctxt
