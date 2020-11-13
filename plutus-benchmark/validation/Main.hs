{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import qualified Language.PlutusCore                               as PLC
import qualified Language.PlutusCore.Pretty                        as PP

import           Criterion.Main
import           Criterion.Types                                   (Config (..))
import qualified Language.UntypedPlutusCore                        as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek as UPLC
import           Paths_plutus_benchmark                            (getDataFileName)

import           Control.Monad
import           Control.Monad.Trans.Except                        (runExceptT)
import qualified Data.ByteString.Lazy                              as BSL
import           System.FilePath
import           Text.Printf                                                (printf)
import Text.Show.Pretty
import Data.HashMap.Monoidal (elems, getMonoidalHashMap, MonoidalHashMap)
import Language.PlutusCore.Evaluation.Machine.ExMemory
import Data.Maybe (fromMaybe)
import Data.Foldable
import PlutusPrelude (traceShowId, coerce, view)
import Control.Lens.Wrapped
import Data.Csv
import qualified Data.HashMap.Monoidal as MHM
import qualified Data.HashMap.Strict as HM
import Data.Bifunctor (Bifunctor(bimap))
import qualified Data.Csv as CSV
import qualified Data.Vector as V
import Data.String (IsString(fromString))
import Data.Hashable
import qualified Data.HashSet as HashSet

{-- | This set of benchmarks is based on validations occurring in the tests in
  plutus-use-cases.  Those tests are run on the blockchain simulator, and a
  modified version of Ledger.Scripts was used to extract validator scripts and
  their arguments.  These are stored in the `data` directory as Plutus Core
  source code, along with README files explaining which scripts were involved in
  each validation during the tests.  --}

type Term a    = UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun a
type Program a = UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun a
type PlcParserError = PLC.Error PLC.DefaultUni PLC.DefaultFun PLC.AlexPosn

loadPlcSource :: FilePath -> IO (Program ())
loadPlcSource file = do
  contents <- BSL.readFile file
  PLC.runQuoteT $ runExceptT (UPLC.parseScoped contents) >>= \case
     Left (err::PlcParserError) -> error $ "Parser error: " ++ PP.displayPlcDef err
     Right p                    -> return $ () <$ p

benchCek :: Term () -> Benchmarkable
benchCek = nf (UPLC.unsafeEvaluateCek PLC.defBuiltinsRuntime)

runForCosts :: Term () -> UPLC.CekExBudgetState PLC.DefaultFun
runForCosts program = snd $ UPLC.runCekCounting PLC.defBuiltinsRuntime program

plcSuffix :: String
plcSuffix = "plc"

-- The name of the directory where the scripts are kept.
-- This must match the location of the files relative to the directory containing the cabal file.
-- IF THE DIRECTORY IS MOVED, THIS MUST BE UPDATED.
scriptDirectory :: String
scriptDirectory = "validation" </> "data"

{- Construct an applied validator.  We assume that relevant validators, datum
   scripts, redeemers and contexts are stored in CBOR format under `<progName>`
   in the `data` directory.  These should have names like "Redeemer01.cbor",
   "Context03.cbor", and so on. This function returnes a Criterion environment
   to be fed to the relevant benchmark, to keep the IO overhead out of the
   benchmark itself. -}
getAppliedScript :: String -> Int -> Int -> Int -> Int -> IO (Term ())
getAppliedScript progName validatorNumber datumNumber redeemerNumber contextNumber = do
  let loadScript base scriptNumber = do
          let file = scriptDirectory </> progName </> (base ++ printf "%02d" scriptNumber) <.> plcSuffix
          dataPath <- getDataFileName file
          loadPlcSource dataPath
  validator <- loadScript "Validator" validatorNumber
  datum     <- loadScript "Datum"     datumNumber
  redeemer  <- loadScript "Redeemer"  redeemerNumber
  context   <- loadScript "Context"   contextNumber
  let appliedValidator = validator `UPLC.applyProgram` datum `UPLC.applyProgram` redeemer `UPLC.applyProgram` context
  pure $ void . UPLC.toTerm $ appliedValidator

{- Create a benchmark with a name like "crowdfunding/5" by applying validator
   number v to datum number d, redeemer number r, and context number c in the
   directory data/<dirname>.  The 'bmId' argument is just to make the names of the
   indvidual benchmarks more readable and more easily typed. -}
mkBM :: String -> (Int, (Int, Int, Int, Int)) -> Benchmark
mkBM dirname (bmId, (v,d,r,c)) =
    env (getAppliedScript dirname v d r c) $ \script -> bench (show bmId) $ benchCek script

instance PrettyVal (UPLC.CekExBudgetState PLC.DefaultFun)
instance PrettyVal UPLC.ExBudget
instance PrettyVal ExCPU
instance PrettyVal ExMemory
instance PrettyVal (UPLC.ExTally (UPLC.ExBudgetCategory PLC.DefaultFun))
instance PrettyVal PLC.DefaultFun
instance PrettyVal (UPLC.ExBudgetCategory PLC.DefaultFun)
instance PrettyVal (MonoidalHashMap (UPLC.ExBudgetCategory PLC.DefaultFun) [UPLC.ExBudget]) where
  prettyVal hm = fromMaybe (String $ show hm) $ parseValue $ show $ getMonoidalHashMap hm

instance PrettyVal (MonoidalHashMap (UPLC.ExBudgetCategory PLC.DefaultFun) UPLC.ExBudget) where
  prettyVal hm = fromMaybe (String $ show hm) $ parseValue $ show $ getMonoidalHashMap hm

hashNub :: forall a. (Eq a, Hashable a) => [a] -> [a]
hashNub = go HashSet.empty
  where
    go :: HashSet.HashSet a -> [a] -> [a]
    go _ []     = []
    go s (x:xs) =
      if x `HashSet.member` s
      then go s xs
      else x : go (HashSet.insert x s) xs

toCPUCSV :: [(String, MonoidalHashMap (UPLC.ExBudgetCategory PLC.DefaultFun) UPLC.ExBudget)] -> BSL.ByteString
toCPUCSV hms = CSV.encodeByName header $ fmap (\(name, hm) -> HM.union (values name hm) baseHM) hms
  where
    values name hm = getMonoidalHashMap $ MHM.insert "Name" name $ MHM.mapKeys keyToStringFn $ fmap (\v -> show $ getExCPU $ UPLC._exBudgetCPU v) hm
    header = V.fromList $ ["Name"] <> (hashNub $ hms >>= (fmap keyToStringFn . MHM.keys . snd))
    baseHM = HM.fromList $ zip (toList header) $ repeat ""
    keyToStringFn = fromString . show

mkC :: String -> (Int, (Int, Int, Int, Int)) -> IO CPUMeasurements
mkC dirname (id, (v,d,r,c)) = do
    state <- runForCosts <$> (getAppliedScript dirname v d r c)
    -- print $ show $ prettyVal state
    pure ((dirname <> "/" <> show id),  fmap fold $ (coerce (view UPLC.exBudgetStateTally state) :: (MonoidalHashMap (UPLC.ExBudgetCategory PLC.DefaultFun) [UPLC.ExBudget])))

writeCPUCSV :: [IO [CPUMeasurements]] -> IO ()
writeCPUCSV ios = do
  measurements <- fmap join $ sequence ios
  BSL.putStr $ toCPUCSV measurements

-- Make a `bgroup` collecting together a number of benchmarks for the same contract
mkBgroup :: String -> [(Int, (Int, Int, Int, Int))] -> Benchmark
mkBgroup dirname bms = bgroup dirname (map (mkBM dirname) bms)


{- | The Criterion configuration returned by `getConfig` will cause an HTML report
   to be generated.  If run via stack/cabal this will be written to the
   `plutus-benchmark` directory by default.  The -o option can be used to change
   this, but an absolute path will probably be required (eg,
   "-o=$PWD/report.html") . -}
getConfig :: IO Config
getConfig = do
  templateDir <- getDataFileName "templates"
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
  pure $ defaultConfig {
                template = templateFile,
                reportFile = Just "report.html"
              }
type CPUMeasurements = (String, MonoidalHashMap (UPLC.ExBudgetCategory PLC.DefaultFun) UPLC.ExBudget)

mkCgroup :: String -> [(Int, (Int, Int, Int, Int))] -> IO [CPUMeasurements]
mkCgroup dirname bms = sequence (map (mkC dirname) bms)

{- See the README files in the data directories for the combinations of scripts.
   you can run specific benchmarks by typing things like
   `stack bench -- plutus-benchmark:validation --ba crowdfunding/2`. -}
main :: IO ()
main = do
  templateDir <- getDataFileName "templates"
  config <- getConfig
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
      -- csvConfig = defaultConfig { csvFile = Just $ "validation.csv" }
  writeCPUCSV
       [ mkCgroup
      --    "crowdfunding"
      --    [ (1, (1,1,1,1))
      --    , (2, (1,2,1,2))
      --    , (3, (1,3,1,3))
      --    , (4, (1,3,2,4))
      --    , (5, (1,1,2,5))
      --    ]
      --  , mkCgroup
         "future"
         [-- (1, (1,1,1,1))
        --  , (2, (2,2,1,2))
        --  , (3, (2,3,1,3))
        --  , (4, (3,4,2,4))
        --  , (5, (3,5,3,5))
        --  , (6, (3,4,4,6))
          (7, (3,4,3,7))
         ]
      --  , mkCgroup
      --    "multisigSM"
      --    [ (1,  (1,1,1,1))
      --    , (2,  (1,2,2,2))
      --    , (3,  (1,3,3,3))
      --    , (4,  (1,4,4,4))
      --    , (5,  (1,5,5,5))
      --    , (6,  (1,1,1,6))
      --    , (7,  (1,2,2,7))
      --    , (8,  (1,3,3,8))
      --    , (9,  (1,4,4,9))
      --    , (10, (1,5,5,10))
      --    ]
      --  , mkCgroup
      --    "vesting"
      --    [ (1,  (1,1,1,1))
      --    , (2,  (2,1,1,2))
      --    , (3,  (3,1,1,1))
      --    ]
      --  , mkCgroup
      --    "marlowe/trustfund"
      --    [ (1,  (1,1,1,1))
      --    , (2,  (1,2,2,2))
      --    ]
      --  , mkCgroup
      --    "marlowe/zerocoupon"
      --    [ (1,  (1,1,1,1))
      --    , (2,  (1,2,2,2))
      --    ]
       ]
  -- defaultMainWith csvConfig
  --      [ mkBgroup
  --        "crowdfunding"
  --        [ (1, (1,1,1,1))
  --        , (2, (1,2,1,2))
  --        , (3, (1,3,1,3))
  --        , (4, (1,3,2,4))
  --        , (5, (1,1,2,5))
  --        ]
  --      , mkBgroup
  --        "future"
  --        [ (1, (1,1,1,1))
  --        , (2, (2,2,1,2))
  --        , (3, (2,3,1,3))
  --        , (4, (3,4,2,4))
  --        , (5, (3,5,3,5))
  --        , (6, (3,4,4,6))
  --        , (7, (3,4,3,7))
  --        ]
  --      , mkBgroup
  --        "multisigSM"
  --        [ (1,  (1,1,1,1))
  --        , (2,  (1,2,2,2))
  --        , (3,  (1,3,3,3))
  --        , (4,  (1,4,4,4))
  --        , (5,  (1,5,5,5))
  --        , (6,  (1,1,1,6))
  --        , (7,  (1,2,2,7))
  --        , (8,  (1,3,3,8))
  --        , (9,  (1,4,4,9))
  --        , (10, (1,5,5,10))
  --        ]
  --      , mkBgroup
  --        "vesting"
  --        [ (1,  (1,1,1,1))
  --        , (2,  (2,1,1,2))
  --        , (3,  (3,1,1,1))
  --        ]
  --      , mkBgroup
  --        "marlowe/trustfund"
  --        [ (1,  (1,1,1,1))
  --        , (2,  (1,2,2,2))
  --        ]
  --      , mkBgroup
  --        "marlowe/zerocoupon"
  --        [ (1,  (1,1,1,1))
  --        , (2,  (1,2,2,2))
  --        ]
  --      ]
