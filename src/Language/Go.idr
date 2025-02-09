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



namespace Context
  public export
  record Context where
    constructor MkContext
    definitions : Definitions
    returnType : Types
    serial : Nat

  public export
  data AddDefinition : (oldCtxt : Context) ->
                       (kind : Kind) ->
                       (ty : Ty) ->
                       (newCtxt : Context) ->
                       Type where
    NewDeBruijn : AddDefinition oldCtxt kind ty (MkContext
                    (oldCtxt.definitions :< Define kind newTy oldCtxt.serial)
                    oldCtxt.returnType
                    (S oldCtxt.serial))


namespace Expr
  public export
  data Expr : (ctxt : Context) -> (res : Types) -> Type where
    IntLiteral  : (x : Nat) -> Expr ctxt [<Int']
    BoolLiteral : (x : Bool) -> Expr ctxt [<Bool']
    GetVar : (idx : Depth ctxt.definitions) ->
             DefTypeIs ctxt.definitions idx ty =>
             Expr ctxt [<ty]


namespace Block
  public export
  data AllowJustStop : (ctxt : Context) ->
                       (isTerminating : Bool) ->
                       Type where
    StopWhenNonTerminating : AllowJustStop _ False
    StopWhenReturnNone : AllowJustStop (MkContext _ [<] _) isTerminating


  public export
  data AllowInnerIf : (isTerminatingThen : Bool) ->
                      (isTerminatingElse : Bool) ->
                      Type where
    InnerIfCC : AllowInnerIf False False
    InnerIfCT : AllowInnerIf False True
    InnerIfTC : AllowInnerIf True False


  mutual
    public export
    data Block : (ctxt : Context) ->
                 (isReturning : Bool) ->
                 Type where

      JustStop : AllowJustStop ctxt isTerminating =>
                 Block ctxt isTerminating

      Return : (res : Expr (MkContext defs ret ser) ret) ->
               Block (MkContext defs ret ser) True

      InnerIf : (test : Expr ctxt [<Bool']) ->
                AllowInnerIf isTerminatingThen isTerminatingElse =>
                (th : Block ctxt isTerminatingThen) ->
                (el : Block ctxt isTerminatingElse) ->
                (cont : Block ctxt isTerminating) ->
                Block ctxt isTerminating

      TermIf : (test : Expr ctxt [<Bool']) ->
               (th : Block ctxt True) ->
               (el : Block ctxt True) ->
               Block ctxt True

      -- Expr : (expr : Expr ctxt [<]) -> Block ctxt False

      InitVar : {oldCtxt, newCtxt : Context} ->
                (newTy : Ty) ->
                (initVal : Expr oldCtxt [<newTy]) ->
                {auto pr : AddDefinition oldCtxt Var newTy newCtxt} ->
                (cont : Block newCtxt isRet) ->
                Block oldCtxt isRet

  export
  isEmpty : Block _ _ -> Bool
  isEmpty JustStop = True
  isEmpty _ = False

export
genBlocks : Fuel -> (ctxt : Context) -> (isTerminating : Bool) ->
            Gen MaybeEmpty $ Block ctxt isTerminating
