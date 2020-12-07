{- Perform various transformations on the ASTs for the validators of
   the sample contracts and print out a markdown table showing how
   these effect the size of the CBOR. -}

{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns    #-}

--{-# OPTIONS_GHC -fno-warn-unused-imports #-}
--{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
--{-# OPTIONS_GHC -fno-warn-unused-matcnhes #-}

{- Typed compression instances are determined in Language.PlutusCore,
   untyped ones in Merkle.Merklise (use CBOR for serilisation including
   unit annotations, CBOR for serilisation omitting units. -}

module CompressionAnalysis (main) where

import qualified Language.PlutusCore                                           as PLC
import qualified Ledger.Crypto
import qualified Ledger.Validation

import           Language.PlutusCore.Untyped.Convert                           as C
import           Language.PlutusCore.Core.Translate                            as Bi
import           Language.PlutusCore.DeBruijn                                  as DB

import           Language.PlutusTx.Coordination.Contracts.Crowdfunding         as Crowdfunding
import           Language.PlutusTx.Coordination.Contracts.Currency             as Currrency
import           Language.PlutusTx.Coordination.Contracts.Escrow               as Escrow
import           Language.PlutusTx.Coordination.Contracts.Future               as Future
import           Language.PlutusTx.Coordination.Contracts.Game                 as Game
import           Language.PlutusTx.Coordination.Contracts.GameStateMachine     as GameStateMachine
import           Language.PlutusTx.Coordination.Contracts.MultiSig             as MultiSig
import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MultiSigStateMachine
import           Language.PlutusTx.Coordination.Contracts.PubKey               as PubKey
import           Language.PlutusTx.Coordination.Contracts.Swap                 as Swap
import           Language.PlutusTx.Coordination.Contracts.TokenAccount         as TokenAccount
import           Language.PlutusTx.Coordination.Contracts.Vesting              as Vesting

import           Language.Marlowe.Semantics                                    as Marlowe

import           Language.PlutusTx                                             as PlutusTx

import qualified Codec.Compression.GZip                                        as G
import           Codec.Serialise                                               (Serialise, serialise, decode, encode)
import qualified Data.ByteString.Lazy                                          as B
import           GHC.Int                                                       (Int64)
import           Numeric

import           Debug.Trace

import qualified Language.PlutusCore.TypeCheck.Bi                              as Bt
import qualified Language.PlutusCore.Core.BiType                               as BLC         

import qualified Data.Text                                                     as T (unpack)

data X = X
instance Serialise X where
    encode = mempty
    decode = pure X
             
{----------------- Analysis -----------------}

printHeader :: IO ()
printHeader = do
  putStrLn "| Contract | Compression | Typed | Typed, stringless names | Untyped | Untyped, stringless names | Untyped, integer IDs only | Untyped, de Bruijn | Bi1 | Bi2 | Bi Stringless | Bi Debruijn |"
  putStrLn "| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
-- ^ The original table had a column at the end for "annotations not serialised".

printHeader2 :: IO ()
printHeader2 = do
  putStrLn "| Contract | Compression | Typed | Typed, minimised |"
  putStrLn "| :---: | ---: | ---: | ---: |"

printSeparator :: IO ()
printSeparator = do
  putStrLn "| |"  -- This is to separate entries in a table.  Two bars seems to be enough (but not one on GitHub).
  putStrLn "| |"  -- A thicker line or something would be better, but I don't think you can do that.

data CompressionMode = Uncompressed | Compressed
data PrintFormat = Alone | WithPercentage

printEntry :: Int64 -> (B.ByteString, PrintFormat) -> CompressionMode -> IO ()
printEntry fullSize (s, mode) cmode = do
  let s' = case cmode of
             Uncompressed -> s
             Compressed   -> G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression} s
  let len = B.length s'
  putStr . show $ len
  case mode of
    Alone -> pure ()
    WithPercentage ->
        putStr $ " (" ++ Numeric.showFFloat (Just 1) (percentage len) "%" ++ ")"
        where percentage n = 100.0 * (fromIntegral n) / (fromIntegral fullSize) :: Float

printInfo1 :: Int64 -> [(B.ByteString, PrintFormat)] -> CompressionMode -> IO ()
printInfo1 _fullSize [] _ = putStrLn ""
printInfo1 fullSize (i : rest) cmode = do
  printEntry fullSize i cmode
  putStr " | "
  printInfo1 fullSize rest cmode

printInfo :: Int64 -> [(B.ByteString, PrintFormat)] -> IO ()
printInfo fullSize entries = do
  putStr " Uncompressed | "
  printInfo1 fullSize entries Uncompressed
  putStr "|     | Compressed | "
  printInfo1 fullSize entries Compressed


-- Print out various compression statistics for a program.  By
-- default, serialisation will include units.  To omit units, replace
-- the import Erasure.Untyped.CBOR by Erasure.Untyped.CBOR2 in
-- Language.PlutusCore.Merkle.Merklise This will entail a lot of
-- recompilation.

analyseCompression :: String -> PLC.Program PLC.TyName PLC.Name () -> IO ()
analyseCompression name prog = do
  let s1 = serialise prog  -- This will use
      s2 = serialise . C.removeNameStrings $ prog
      s3 = serialise . C.erasePLCProgram $ prog
      s4 = serialise . C.erasePLCProgram . C.removeNameStrings $ prog
      s5 = serialise . C.nameToIntProgram . C.erasePLCProgram $ prog
      s6 = serialise . C.deBruijnToIntProgram . C.erasePLCProgram . C.deBruijnPLCProgram $ prog
      s7 = serialise . Bi.transProg $ prog
      s8 = serialise . Bi.transProg2 $ prog
      s9 = serialise . C.removeNameStringsBi . Bi.transProg2 $ prog
      s0 = serialise . DB.deBruijnBiPLCProgram . Bi.transProg2 $ prog
  -- let !_ = traceShow (dbShow' prog) False
  -- let !_ = traceShow "\n\n\n\n\n%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n\n\n\n" False
  -- let !bp = Bi.transProg prog
  -- let !_ = traceShow (dbShow bp) False
  -- let !_ = traceShow "Country road lets'a go" False
  -- let !_ = Bt.typeCheck bp
  --let !_ = Bt.typeCheck $ Bi.transProg2 prog
  putStr $ "| " ++ name ++ " | "
  printInfo (B.length s1) [(s1, Alone), (s2, Alone), (s3, WithPercentage), (s4, Alone), (s5, WithPercentage), (s6, WithPercentage), (s7, WithPercentage), (s8, WithPercentage), (s9, WithPercentage), (s0, WithPercentage)]
  pure ()

analyseProg :: String -> CompiledCode a -> IO ()
analyseProg name prg = do
  analyseCompression name $ PlutusTx.getPlc prg


analyseCompression2 :: String -> PLC.Program PLC.TyName PLC.Name () -> IO ()
analyseCompression2 name prog = do
  let s1 = serialise prog
      s2 = serialise . C.deBruijnToIntPLCProgram . C.deBruijnPLCProgram $ prog
  putStr $ "| " ++ name ++ " | "
  printInfo (B.length s1) [(s1, Alone), (s2, WithPercentage)]


analyseProg2 :: String -> CompiledCode a -> IO ()
analyseProg2 name prg = do
  analyseCompression2 name $ PlutusTx.getPlc prg

compiledMarloweValidator :: CompiledCode (Ledger.Crypto.PubKey
                                     -> MarloweData -> [Input]
                                     -> Ledger.Validation.PendingTx -> Bool)

compiledMarloweValidator = $$(PlutusTx.compile [|| Marlowe.marloweValidator ||])

data Counts = Counts Integer Integer Integer Integer
                           
instance Semigroup Counts
    where (Counts a b c d) <> (Counts x y z t) = Counts (a+x) (b+y) (c+z) (d+t)

instance Monoid Counts
    where mempty = Counts 0 0 0 0

analyseTypeApplications :: PLC.Term tyname name () -> Counts
analyseTypeApplications = f 
    where f = \case
              PLC.Var{}              -> mempty
              PLC.Constant{}         -> mempty
              PLC.Builtin{}          -> mempty
              PLC.Error _ _          -> mempty
              PLC.LamAbs _ _ _ t     -> f t
              PLC.Unwrap _ t         -> f t
              PLC.IWrap _ _ _ t      -> f t
              PLC.Apply _ t t'       -> f t <> f t'
              PLC.TyAbs _ _ _ t      -> f t <> Counts 1 0 0 0
              PLC.TyInst _ t _       ->
                  case t of
                    PLC.TyAbs {} -> f t <> Counts 0 1 1 0
                    PLC.Var {}   -> Counts 0 1 0 1
                    _ -> f t <> Counts 0 1 0 0

-- {(abs alpha K M) A} -> M
                                  
analyseTyApps :: String -> CompiledCode a -> IO ()
analyseTyApps name prg = do
  let PLC.Program _ _ body = PlutusTx.getPlc prg
      Counts appcount instcount instappcount instvarcount = analyseTypeApplications body
  putStrLn $ name ++ ": " ++ show appcount ++ "/" ++ show instcount ++ "/" ++ show instappcount ++ "/" ++ show instvarcount

main :: IO ()
main = do
  printHeader
  analyseProg    "Crowdfunding"         Crowdfunding.exportedValidator
  printSeparator
  analyseProg    "Currrency"            Currrency.exportedValidator
  printSeparator
  analyseProg    "Escrow"               Escrow.exportedValidator
  printSeparator
  analyseProg    "Future"               Future.exportedValidator
  printSeparator
  analyseProg    "Game"                 Game.exportedValidator
  printSeparator
  analyseProg    "GameStateMachine"     GameStateMachine.exportedValidator
  printSeparator
  analyseProg    "MultiSig"             MultiSig.exportedValidator
  printSeparator
  analyseProg    "MultiSigStateMachine" MultiSigStateMachine.exportedValidator
  printSeparator
  analyseProg    "PubKey"               PubKey.exportedValidator
  printSeparator
  analyseProg    "Swap"                 Swap.exportedValidator
  printSeparator
  analyseProg    "TokenAccount"         TokenAccount.exportedValidator
  printSeparator
  analyseProg    "Vesting"              Vesting.exportedValidator
  printSeparator
  analyseProg    "Marlowe"              compiledMarloweValidator

-- Current validator is a little different for Future and PubKey

-- See plutus-use-cases/bench/Bench.hs for examples of manipulating PLC code


{-

-- PlutusCore with CBOR
| Contract | Compression  | Typed  | Typed, stringless | Untyped | Untyped, stringless | Untyped, integer IDs only | Untyped, de Bruijn |

| Marlowe |  Uncompressed | 449965 | 245720 | 141513 | 71233 | 61048 (13.6%) | 46584 (10.4%) | 
|         |    Compressed |  72878 |  58568 |  30425 | 22760 |  22511 (5.0%) |   7882 (1.8%) | 

-- PlutusCore with CBOR2
 
| Marlowe |  Uncompressed | 354910 | 182853 | 131328 | 71233 | 61048 (17.2%) | 46584 (13.1%) | 
|         |    Compressed |  69715 |  55922 |  30010 | 22760 |  22511 (6.3%) |   7882 (2.2%) | 

-}

dbShow :: BLC.BiProgram PLC.TyName PLC.Name () -> String
dbShow = s . BLC.toTerm
  where s :: BLC.BiTerm PLC.TyName PLC.Name () -> String
        s (BLC.BiVar _ n) = sn n
        s (BLC.BiLamAbs _ n tm) = "( \\ " ++ sn n ++ ". " ++ s tm ++ ")"
        s (BLC.BiApply _ fun arg) = "(App " ++ s fun ++ " #> " ++ s arg ++ ")"
        s (BLC.BiConstant _ c) = "(Const " ++ show c ++ ")"
        s (BLC.BiBuiltin _ b) = "(Bltin " ++ show b ++ ")"
        s (BLC.BiUnwrap _ tm) = "(Unwrap " ++ s tm ++ ")"
        s (BLC.BiIWrap _ ty1 ty2 tm) = "(IWrap " ++ t ty1 ++ " @> " ++ t ty2 ++ ")"
        s (BLC.BiError _ ty) = "(Error " ++ t ty ++ ")"
        s (BLC.TyAnn _ tm ty) = "(Ann " ++ s tm ++ " ;; " ++ t ty ++ ")" 
        t :: PLC.Type PLC.TyName () -> String
        t (PLC.TyVar _ n) = tn n
        t (PLC.TyFun _ arg res) = "(" ++ t arg ++ " -> " ++ t res ++ ")"
        t (PLC.TyIFix _ ty1 ty2) = "(IFix " ++ t ty1 ++ " @@ " ++ t ty2 ++ ")"
        t (PLC.TyForall _ n k ty) = "(\\/ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (PLC.TyBuiltin _ n) = "(TBtin " ++ show n ++ ")"
        t (PLC.TyLam _ n k ty) = "( /\\ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (PLC.TyApp _ fun arg) = "(TApp " ++ t fun ++ " ## " ++ t arg ++ ")" 
        sn :: PLC.Name () -> String
        sn n = (T.unpack $ PLC.nameString n) ++ "_" ++ (show $ PLC.unUnique $ PLC.nameUnique n)
        tn :: PLC.TyName () -> String
        tn = sn . PLC.unTyName

dbShow' :: PLC.Program PLC.TyName PLC.Name () -> String
dbShow' (PLC.Program _ _ tm) = s tm
  where s :: PLC.Term PLC.TyName PLC.Name () -> String
        s (PLC.Var _ n) = sn n
        s (PLC.LamAbs _ n ty tm) = "( \\ " ++ sn n ++ " : " ++ t ty ++ ". " ++ s tm ++ ")"
        s (PLC.Apply _ fun arg) = "(App " ++ s fun ++ " #> " ++ s arg ++ ")"
        s (PLC.Constant _ c) = "(Const " ++ show c ++ ")"
        s (PLC.Builtin _ b) = "(Bltin " ++ show b ++ ")"
        s (PLC.Unwrap _ tm) = "(Unwrap " ++ s tm ++ ")"
        s (PLC.IWrap _ ty1 ty2 tm) = "(IWrap " ++ t ty1 ++ " @> " ++ t ty2 ++ ")"
        s (PLC.Error _ ty) = "(Error " ++ t ty ++ ")"
        s (PLC.TyAbs _ n k tm) = "( /\\ " ++ tn n ++ ". " ++ s tm ++")"
        s (PLC.TyInst _ tm ty) = "(TyApp " ++ s tm ++ " $$ " ++ t ty ++ ")"
        t :: PLC.Type PLC.TyName () -> String
        t (PLC.TyVar _ n) = tn n
        t (PLC.TyFun _ arg res) = "(" ++ t arg ++ " -> " ++ t res ++ ")"
        t (PLC.TyIFix _ ty1 ty2) = "(IFix " ++ t ty1 ++ " @@ " ++ t ty2 ++ ")"
        t (PLC.TyForall _ n k ty) = "(\\/ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (PLC.TyBuiltin _ n) = "(TBtin " ++ show n ++ ")"
        t (PLC.TyLam _ n k ty) = "( /\\ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (PLC.TyApp _ fun arg) = "(TApp " ++ t fun ++ " ## " ++ t arg ++ ")" 
        sn :: PLC.Name () -> String
        sn n = (T.unpack $ PLC.nameString n) ++ "_" ++ (show $ PLC.unUnique $ PLC.nameUnique n)
        tn :: PLC.TyName () -> String
        tn = sn . PLC.unTyName