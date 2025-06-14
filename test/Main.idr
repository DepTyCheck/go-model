module Main

import System
import System.Directory
import System.File

import Test.Golden.RunnerHelper

%default covering
main : IO ()
main = goldenRunner $
  [ "Check Order" `atDir` "01-check-order"
  -- , "Pretty Printing" `atDir` "02-pretty-print"
  ]
