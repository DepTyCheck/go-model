module Language.Go.DSL

import Language.Go.Model
-- import Language.Go.Aux

export
infixl 8 .+.

export
(.+.) : {ctxt : Context} ->
        Expr ctxt [GoInt] -> Expr ctxt [GoInt] -> Expr ctxt [GoInt]
(.+.) = ApplyInfix IntAdd

-- @WHEN EXTRA_BUILTINS
-- @ export
-- @ infixl 8 .-.

-- @ export
-- @ infixl 9 .*.

-- @ export
-- @ infixl 5 .&&.

-- @ export
-- @ infixl 4 .||.

-- @ export
-- @ (.-.), (.*.) : {ctxt : Context} ->
               -- @ Expr ctxt [GoInt] -> Expr ctxt [GoInt] -> Expr ctxt [GoInt]
-- @ (.-.) = ApplyInfix IntSub
-- @ (.*.) = ApplyInfix IntMul
-- @END EXTRA_BUILTINS

export
print : {ctxt : Context} -> Expr ctxt [GoInt] -> Expr ctxt []
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
