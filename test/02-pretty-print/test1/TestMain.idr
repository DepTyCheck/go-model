import Language.Go


longExpr : forall ctxt. Expr ctxt [GoInt]
longExpr = 1 .+. 2 .+. 3 .+. 4 .+. 5

longDecl : Statement EmptyContext
longDecl =
  Var' _ longExpr JustStop


main : IO ()
main = ?todo

