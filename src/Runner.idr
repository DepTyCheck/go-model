module Runner

import Data.Fuel
import Data.List.Lazy

import Language.Go
import Language.Go.Derived

import System.Random.Pure.StdGen

import Test.DepTyCheck.Gen

export
main : IO ()
main = do
  seed <- initSeed
  let testCnt = 10
  let modelFuel = limit 10_000
  let vals = unGenTryN testCnt seed $ genBlocks modelFuel () Int'
  Lazy.for_ vals $ \val => do
    putStrLn "Done"
