module Language.Go.Pretty.Go

import Language.Go

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen
import Deriving.DepTyCheck.Gen

public export
printGo : Fuel -> Block ctxt ret -> Gen0 $ Doc opts
printGo _ block = pure "Done"
