module Language.Go.DSL

import Data.Fin

import Language.Go.Model
import Language.Go.Aux


%unbound_implicits off


parameters {0 ctxt : Context}
  export
  %inline
  fromInteger : Integer -> Expr ctxt [GInt]
  fromInteger x = GetLiteral $ MkInt $ fromInteger x


  export
  %inline
  true, false : Expr ctxt [GBool]
  true = GetLiteral $ MkBool True
  false = GetLiteral $ MkBool False


  export
  infixl 8 .+.

  export
  (.+.) : Expr ctxt [GInt] -> Expr ctxt [GInt] -> Expr ctxt [GInt]
  (.+.) = ApplyInfix IntAdd

  -- @WHEN EXTRA_BUILTINS
-- @   export
-- @   infixl 8 .-.

-- @   export
-- @   infixl 9 .*.

-- @   export
-- @   infixl 5 .&&.

-- @   export
-- @   infixl 4 .||.

-- @   export
-- @   (.-.), (.*.) : {ctxt : Context} ->
-- @                  Expr ctxt [GInt] -> Expr ctxt [GInt] -> Expr ctxt [GInt]
-- @   (.-.) = ApplyInfix IntSub
-- @   (.*.) = ApplyInfix IntMul
  -- @END EXTRA_BUILTINS

  export
  print : Expr ctxt [GInt] -> Expr ctxt []
  print = CallBuiltin Print

-- export
-- get : {ctxt : Context} ->
--       {height : Nat} ->
--       (RelativeTo height) ->
--       Expr ctxt ?___

-- main : Go
-- main = do
--   avg <- func (withNewNames [GoDouble, GoDouble]) $ \[x, y] => do
--     res <- var ((x .+. y) ./. 2)
--     return $ get res

--   main <- func [] $ \[] => do
--     void $ print "Hello, World"