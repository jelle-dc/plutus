{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE FlexibleInstances #-}
module Language.PlutusTx.Bench.Bi where

import qualified Language.PlutusTx.Coordination.Contracts.Crowdfunding as CF
import qualified Language.PlutusTx.Coordination.Contracts.Game as G
import qualified Language.PlutusTx.Coordination.Contracts.GameStateMachine as GSM

import PlutusPrelude
  
import Language.PlutusTx
import Language.PlutusTx.Code
  
import Ledger.Scripts
import Ledger.Typed.Scripts

import Language.PlutusCore.Core
import Language.PlutusCore.Name
import Language.PlutusCore.CBOR
import Language.PlutusCore.Core.Translate
import Language.PlutusCore.Universe
import Language.PlutusCore.TypeCheck
import qualified Language.PlutusCore.Error as E
import Language.PlutusCore.Quote
import Language.PlutusCore.Constant.Dynamic

import Codec.Serialise

import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BSL

serializedSize :: Serialise a => a -> Integer
serializedSize = fromIntegral . BSL.length . serialise

crowd = unScript $ unValidatorScript $ validatorScript $ CF.scriptInstance CF.theCampaign

crowdSize    = serializedSize              crowd
biCrowdSize  = serializedSize $ transProg  crowd
biCrowdSize2 = serializedSize $ transProg2 crowd
biCrowdSize3 = serializedSize $ transProg3 crowd
biCrowdSize4 = serializedSize $ transProg4 crowd
eCrowdSize   = serializedSize $ eProg $ transProg crowd
dCrowdSize   = serializedSize $ deBruijnConcrete crowd

game = unScript $ unValidatorScript G.gameValidator

gameSize    = serializedSize              game
biGameSize  = serializedSize $ transProg  game
biGameSize2 = serializedSize $ transProg2 game
biGameSize3 = serializedSize $ transProg3 game
biGameSize4 = serializedSize $ transProg4 game
eGameSize   = serializedSize $ eProg $ transProg game
dGameSize   = serializedSize $ deBruijnConcrete game

gameSM = unScript $ unValidatorScript $ validatorScript $ GSM.scriptInstance
  
gameSMSize    = serializedSize              gameSM
biGameSMSize  = serializedSize $ transProg  gameSM
biGameSMSize2 = serializedSize $ transProg2 gameSM
biGameSMSize3 = serializedSize $ transProg3 gameSM
biGameSMSize4 = serializedSize $ transProg4 gameSM 
eGameSMSize   = serializedSize $ eProg $ transProg gameSM
dGameSMSize   = serializedSize $ deBruijnConcrete gameSM

integerIdentity :: CompiledCode DefaultUni (Integer -> Integer)
integerIdentity = $$(compile [|| \(x:: Integer) -> x ||])

idSize = case integerIdentity of
  DeserializedCode p _ -> serializedSize p
  SerializedCode   p _ -> fromIntegral $ BS.length p
  
biIdSize = case integerIdentity of
  DeserializedCode p _ -> serializedSize $ transProg p
  SerializedCode   p _ -> serializedSize $ transProg $ deserialise $ BSL.fromStrict p

iid = case integerIdentity of
  DeserializedCode p _ -> p
  SerializedCode   p _ -> deserialise $ BSL.fromStrict p
biIid = transProg iid  

typeCheckConcrete :: Program TyName Name DefaultUni ()
                  -> Either (E.Error DefaultUni ()) (Normalized (Type TyName DefaultUni ()))
typeCheckConcrete p = runQuoteT $ do
  bis <- getStringBuiltinTypes ()
  inferTypeOfProgram (defOffChainConfig { _tccDynamicBuiltinNameTypes = bis }) p

div' :: Integer -> Integer -> Double
div' a b = (fromIntegral a) / (fromIntegral b)

main :: IO ()
main = do putStrLn $ "CrowdFunding:     " ++ (show crowdSize)
          putStrLn $ "Bi:               " ++ (show biCrowdSize)  ++ " | "
                                          ++ (show $ biCrowdSize  `div'` crowdSize)
          putStrLn $ "Bi2:              " ++ (show biCrowdSize2) ++ " | "
                                          ++ (show $ biCrowdSize2 `div'` crowdSize)
          putStrLn $ "Bi3:              " ++ (show biCrowdSize3) ++ " | "
                                          ++ (show $ biCrowdSize3 `div'` crowdSize)
          putStrLn $ "Bi4:              " ++ (show biCrowdSize4) ++ " | "
                                          ++ (show $ biCrowdSize4 `div'` crowdSize)
          putStrLn $ "Erased:           " ++ (show eCrowdSize)   ++ " | "
                                          ++ (show $ eCrowdSize   `div'` crowdSize)
          putStrLn $ "Debruijn:         " ++ (show dCrowdSize)   ++ " | "
                                          ++ (show $ dCrowdSize   `div'` crowdSize)
          putStrLn $ "Game:             " ++ (show gameSize)
          putStrLn $ "Bi:               " ++ (show biGameSize)  ++ " | "
                                          ++ (show $ biGameSize  `div'` gameSize)
          putStrLn $ "Bi2:              " ++ (show biGameSize2) ++ " | "
                                          ++ (show $ biGameSize2 `div'` gameSize)
          putStrLn $ "Bi3:              " ++ (show biGameSize3) ++ " | "
                                          ++ (show $ biGameSize3 `div'` gameSize)
          putStrLn $ "Bi4:              " ++ (show biGameSize4) ++ " | "
                                          ++ (show $ biGameSize4 `div'` gameSize)
          putStrLn $ "Erased:           " ++ (show eGameSize)   ++ " | "
                                          ++ (show $ eGameSize   `div'` gameSize)
          putStrLn $ "Debruijn:         " ++ (show dGameSize)   ++ " | "
                                          ++ (show $ dGameSize   `div'` gameSize)
          putStrLn $ "GameStateMachine: " ++ (show gameSMSize)
          putStrLn $ "Bi:               " ++ (show biGameSMSize)  ++ " | "
                                          ++ (show $ biGameSMSize  `div'` gameSMSize)
          putStrLn $ "Bi2:              " ++ (show biGameSMSize2) ++ " | "
                                          ++ (show $ biGameSMSize2 `div'` gameSMSize)
          putStrLn $ "Bi3:              " ++ (show biGameSMSize3) ++ " | "
                                          ++ (show $ biGameSMSize3 `div'` gameSMSize)
          putStrLn $ "Bi4:              " ++ (show biGameSMSize4) ++ " | "
                                          ++ (show $ biGameSMSize4 `div'` gameSMSize)
          putStrLn $ "Erased:           " ++ (show eGameSMSize)   ++ " | "
                                          ++ (show $ eGameSMSize   `div'` gameSMSize)
          putStrLn $ "Debruijn:         " ++ (show dGameSMSize)   ++ " | "
                                          ++ (show $ dGameSMSize   `div'` gameSMSize)
