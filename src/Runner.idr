module Runner

import Data.Fuel
import Data.List.Lazy
import Data.List1
import Data.SortedMap
import Data.String

import Language.Go

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy

import System
import System.GetOpts
import System.Random.Pure.StdGen

%default total

-------------------
--- CLI options ---
-------------------

record Config where
  constructor MkConfig
  usedSeed : IO StdGen
  layoutOpts : LayoutOpts
  testsCnt   : Nat
  modelFuel  : Fuel
  context    : Context


defaultConfig : Config
defaultConfig = MkConfig
  { usedSeed = initSeed
  , layoutOpts = Opts 80
  , testsCnt   = 5
  , modelFuel  = limit 4
  , context    = defaultContext
  }

parseSeed : String -> Either String $ Config -> Config
parseSeed str = do
  let n1:::n2::[] = trim <$> split (== ',') str
    | _ => Left "we expect two numbers divided by a comma"
  let Just n1 = parsePositive n1
    | Nothing => Left "expected a positive number at the first component, given `\{n1}`"
  let Just n2 = parsePositive {a=Bits64} n2
    | Nothing => Left "expected a positive number at the second component, given `\{n2}`"
  let Yes prf = decSo $ testBit n2 0
    | No _ => Left "second component must be odd"
  Right {usedSeed := pure $ rawStdGen n1 n2}

parsePPWidth : String -> Either String $ Config -> Config
parsePPWidth str = case parsePositive str of
  Just n  => Right {layoutOpts := Opts n}
  Nothing => Left "can't parse max width for the pretty-printer"

parseTestsCount : String -> Either String $ Config -> Config
parseTestsCount str = case parsePositive str of
  Just n  => Right {testsCnt := n}
  Nothing => Left "can't parse given count of tests"

parseModelFuel : String -> Either String $ Config -> Config
parseModelFuel str = case parsePositive str of
  Just n  => Right {modelFuel := limit n}
  Nothing => Left "can't parse given model fuel"

cliOpts : List $ OptDescr $ Config -> Config
cliOpts =
  [ MkOpt [] ["seed"]
      (ReqArg' parseSeed "<seed>,<gamma>")
      "Sets particular random seed to start with."
  , MkOpt ['w'] ["pp-width"]
      (ReqArg' parsePPWidth "<nat>")
      "Sets the max length for the pretty-printer."
  , MkOpt ['n'] ["tests-count"]
      (ReqArg' parseTestsCount "<tests-count>")
      "Sets the count of tests to generate."
  , MkOpt [] ["model-fuel"]
      (ReqArg' parseModelFuel "<fuel>")
      "Sets how much fuel there is for generation of the model."
  ]

---------------
--- Running ---
---------------

run : Config -> IO ()
run conf = do
  seed <- conf.usedSeed
  let vals := unGenTryN conf.testsCnt seed $ do
    stmt <- genBlocks conf.modelFuel 0 conf.context True
    code <- wrapBlock {ctxt = conf.context} {opts = conf.layoutOpts} stmt
    let desc := eval stmt
    pure (code, desc)
  Lazy.for_ vals $ \(code, desc) => do
    putStrLn "-//- CODE -//-\n"
    putStrLn $ render conf.layoutOpts code
    putStrLn "-//- DESCRIPTION -//-\n"
    putStrLn desc

---------------
--- Startup ---
---------------

export
main : IO ()
main = do
  args <- getArgs
  let exe_name : String  := fromMaybe "pil-fun" $ head' args
  let usage : Lazy String := usageInfo "Usage: \{exe_name} [options] <language>" cliOpts
  let MkResult options [] [] [] = getOpt Permute cliOpts $ drop 1 args
    | MkResult {unrecognized=unrecOpts@(_::_), _} => if "help" `elem` unrecOpts
                                                       then putStrLn usage
                                                       else die "unrecodnised options \{show unrecOpts}\n\{usage}"
    | MkResult {errors=es@(_::_), _}              => die "arguments parse errors \{show es}\n\{usage}"
    | MkResult _ nonOptions _ _ => die "unexpected non options: \{show nonOptions}"
  let config = foldl (flip apply) defaultConfig options
  run config
