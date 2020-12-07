{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE OverloadedStrings     #-}

module Language.PlutusCore.Core.Translate where

import PlutusPrelude
  
import Language.PlutusCore.Name
import Language.PlutusCore.Error

import Language.PlutusCore.Core.Type
import Language.PlutusCore.Core.BiType

import Language.PlutusCore.TypeCheck
import Language.PlutusCore.TypeCheck.Internal

import Language.PlutusCore.Constant.Dynamic.OffChain

import Language.PlutusCore.Rename

import Language.PlutusCore.Quote

import Language.PlutusCore.DeBruijn
  
import Control.Monad.Except
import Data.Text (pack, unpack)
  
data Mode = Check | Synth
 
isMonoTy :: Type TyName () -> Bool
isMonoTy (TyForall _ _ _ _) = False
isMonoTy (TyLam _ _ _ _)    = False
isMonoTy (TyApp _ _ _)      = False
isMonoTy (TyIFix _ _ _)     = False
isMonoTy (TyFun _ arg res)  = isMonoTy arg && isMonoTy res
isMonoTy _                  = True

-- translate :: Program tyname name uni ann -> BiProgram tyname name uni ann
-- translate (Program ann ver tm) = BiProgram ann ver (transTm Synth tm)

transTm :: Term TyName Name ann
        -> Mode
        -> TypeCheckM ann (Type TyName (), BiTerm TyName Name ())

transTm (Var ann name) _             = do
  (Normalized ty) <- lookupVarM name
  return  (ty, (BiVar () (void name)))

transTm (TyAbs ann n k tm) mode = do
  let k' = void k
  (ty, tmBi) <- withTyVar n k' (transTm tm Check)
  let ty'  = TyForall () (void n) k' ty
  case mode of
    Synth -> return (ty', TyAnn () tmBi ty')
    Check -> return (ty', tmBi)
    
transTm (LamAbs ann n dom body) mode = do
  (Normalized vDom) <- normalizeTypeOptM $ void dom
  (cDom, biBody) <- withVar n (Normalized vDom) (transTm body Check)
  let ty    = TyFun () vDom cDom
      biTm' = BiLamAbs () (void n) biBody
      biTm  = case mode of
        Synth -> TyAnn () biTm' ty
        Check -> biTm'
      in return (ty, biTm)
      
transTm (Apply ann fun arg)     _    = do
  (funTy, biFun) <- transTm fun Synth
  (argTy, biArg) <- case isMonoTy funTy of
                      True  -> transTm arg Check
                      False -> transTm arg Synth
  case funTy of
    TyFun _ _ cod -> return (cod, BiApply () biFun biArg)

transTm (Constant ann con)      _    = do
  let Normalized ty = typeOfConstant con
  return (ty, (BiConstant () (void con)))

transTm (Builtin ann b)         _    = do
  Normalized ty <- inferTypeOfBuiltinM b
  return (ty, BiBuiltin () (void b))

transTm (TyInst ann tm ty)      mode = do
  (biTy, biTm) <- transTm tm Synth
  case biTy of
    TyForall ann' n nk vCod -> do
      vTy <- normalizeTypeOptM $ void ty
      Normalized nTy <- substNormalizeTypeM vTy n vCod
      --return (nTy, biTm)
      case mode of
        Synth -> return (nTy, TyAnn () biTm nTy)
        Check -> return (nTy, biTm)

transTm (Unwrap ann tm)         mode = do
  (tmTy, biTm) <- transTm tm Check
  Normalized ty <- case tmTy of
    TyIFix _ vPat vArg -> do
      k <- inferKindM $ ann <$ vArg
      unfoldFixOf (Normalized vPat) (Normalized vArg) k
    _                  -> throwError (TypeMismatch ann (void tm) (TyIFix () dummyType dummyType) (Normalized tmTy))
  case mode of
    Synth -> return (ty, TyAnn () biTm ty)
    Check -> return (ty, biTm)

transTm (IWrap ann pat arg tm)  mode = do
  Normalized vPat <- normalizeTypeOptM $ void pat
  Normalized vArg <- normalizeTypeOptM $ void arg
  (ty, biTm) <- transTm tm Check -- type can be derived from IWrap
  case mode of
    Synth -> return (ty, TyAnn () biTm ty)
    Check -> return (ty, biTm)
  
transTm (Error ann ty)          _    = do
  Normalized ty' <- normalizeTypeOptM $ void ty
  return (ty', BiError () ty')

-- ---------------------------------------------------------------------------
  
transTm2 :: Term TyName Name ann
         -> Mode
         -> TypeCheckM ann (Type TyName (), BiTerm TyName Name ())

transTm2 (Var ann name) _             = do
  (Normalized ty) <- lookupVarM name
  return  (ty, (BiVar () (void name)))

transTm2 (TyAbs ann n k tm) mode = do
  let k' = void k
  (ty, tmBi) <- withTyVar n k' (transTm2 tm Check)
  let ty'  = TyForall () (void n) k' ty
  case mode of
    Synth -> return (ty', TyAnn () tmBi ty')
    Check -> return (ty', tmBi)
    
transTm2 (LamAbs ann n dom body) mode = do
  (Normalized vDom) <- normalizeTypeOptM $ void dom
  (cDom, biBody) <- withVar n (Normalized vDom) (transTm2 body Check)
  let ty    = TyFun () vDom cDom
      biTm' = BiLamAbs () (void n) biBody
      biTm  = case mode of
        Synth -> TyAnn () biTm' ty
        Check -> biTm'
      in return (ty, biTm)
      
transTm2 (Apply ann fun arg)     mode = do
  (funTy, biFun) <- transTm2 fun Check
  (argTy, biArg) <- transTm2 arg Synth
  let (TyFun _ _ cod) = funTy
      biTm = case mode of
               Synth -> TyAnn () (BiApply () biFun biArg) cod
               Check -> BiApply () biFun biArg
      in return (cod, biTm)

transTm2 (Constant ann con)      _    = do
  let Normalized ty = typeOfConstant con
  return (ty, (BiConstant () (void con)))

transTm2 (Builtin ann b)         _    = do
  Normalized ty <- inferTypeOfBuiltinM b
  return (ty, BiBuiltin () (void b))

transTm2 (TyInst ann tm ty)      mode = do
  (biTy, biTm) <- transTm2 tm Synth
  case biTy of
    TyForall ann' n nk vCod -> do
      vTy <- normalizeTypeOptM $ void ty
      Normalized nTy <- substNormalizeTypeM vTy n vCod
--      return (nTy, biTm)
      case mode of
        Synth -> return (nTy, TyAnn () biTm nTy)
        Check -> return (nTy, biTm)

transTm2 (Unwrap ann tm)         mode = do
  (tmTy, biTm) <- transTm2 tm Check
  Normalized ty <- case tmTy of
    TyIFix _ vPat vArg -> do
      k <- inferKindM $ ann <$ vArg
      unfoldFixOf (Normalized vPat) (Normalized vArg) k
    _                  -> throwError (TypeMismatch ann (void tm) (TyIFix () dummyType dummyType) (Normalized tmTy))
  case mode of
    Synth -> return (ty, TyAnn () biTm ty)
    Check -> return (ty, biTm)

transTm2 (IWrap ann pat arg tm)  mode = do
  Normalized vPat <- normalizeTypeOptM $ void pat
  Normalized vArg <- normalizeTypeOptM $ void arg
  (ty, biTm) <- transTm2 tm Check -- type can be derived from IWrap
  case mode of
    Synth -> return (ty, TyAnn () biTm ty)
    Check -> return (ty, biTm)
  
transTm2 (Error ann ty)          _    = do
  Normalized ty' <- normalizeTypeOptM $ void ty
  return (ty', BiError () ty')

-- ---------------------------------------------------------------------------
  
transTm3 :: Term TyName Name ann
         -> Mode
         -> TypeCheckM ann (Type TyName (), BiTerm TyName Name ())

transTm3 (Var ann name) _             = do
  (Normalized ty) <- lookupVarM name
  return  (ty, (BiVar () (void name)))

transTm3 (TyAbs ann n k tm) mode = do
  let k' = void k
  (ty, tmBi) <- withTyVar n k' (transTm3 tm Check)
  let ty'  = TyForall () (void n) k' ty
  case mode of
    Synth -> return (ty', TyAnn () tmBi ty')
    Check -> return (ty', tmBi)
    
transTm3 (LamAbs ann n dom body) mode = do
  (Normalized vDom) <- normalizeTypeOptM $ void dom
  (cDom, biBody) <- withVar n (Normalized vDom) (transTm3 body Check)
  let ty    = TyFun () vDom cDom
      biTm' = BiLamAbs () (void n) biBody
      biTm  = case mode of
        Synth -> TyAnn () biTm' ty
        Check -> biTm'
      in return (ty, biTm)
      
transTm3 (Apply ann fun arg)     mode = do
  (funTy, biFun) <- transTm3 fun Check
  (argTy, biArg) <- transTm3 arg Synth
  let (TyFun _ _ cod) = funTy
      biTm = case mode of
               Synth -> TyAnn () (BiApply () biFun biArg) cod
               Check -> BiApply () biFun biArg
      in return (cod, biTm)

transTm3 (Constant ann con)      _    = do
  let Normalized ty = typeOfConstant con
  return (ty, (BiConstant () (void con)))

transTm3 (Builtin ann b)         _    = do
  Normalized ty <- inferTypeOfBuiltinM b
  return (ty, BiBuiltin () (void b))

transTm3 (TyInst ann tm ty)      mode = do
  (biTy, biTm) <- transTm3 tm Synth
  case biTy of
    TyForall ann' n nk vCod -> do
      vTy <- normalizeTypeOptM $ void ty
      Normalized nTy <- substNormalizeTypeM vTy n vCod
      return (nTy, biTm)

transTm3 (Unwrap ann tm)         mode = do
  -- type of Unwrap doesn't depend on tm
  -- so tm can't possibly be checked against checking mode type 
  (tmTy, biTm) <- transTm3 tm Synth
  Normalized ty <- case tmTy of
    TyIFix _ vPat vArg -> do
      k <- inferKindM $ ann <$ vArg
      unfoldFixOf (Normalized vPat) (Normalized vArg) k
    _                  -> throwError (TypeMismatch ann (void tm) (TyIFix () dummyType dummyType) (Normalized tmTy))
  case mode of
    Synth -> return (ty, TyAnn () (BiUnwrap () biTm) ty)
    Check -> return (ty, BiUnwrap () biTm)

transTm3 (IWrap ann pat arg tm)  mode = do
  Normalized vPat <- normalizeTypeOptM $ void pat
  Normalized vArg <- normalizeTypeOptM $ void arg
  -- type of IWrap doesn't depend on tm
  -- so tm can't possibly be checked against checking mode type 
  (ty, biTm) <- transTm3 tm Synth
  case mode of
    Synth -> return (ty, TyAnn () (BiIWrap () vPat vArg biTm) ty)
    Check -> return (ty, BiIWrap () vPat vArg biTm)
  
transTm3 (Error ann ty)          _    = do
  Normalized ty' <- normalizeTypeOptM $ void ty
  return (ty', BiError () ty')
-- -------------------------------------------------------------------------------------

  
transTm4 :: Term TyName Name ann
         -> Mode
         -> TypeCheckM ann (Type TyName (), BiTerm TyName Name ())

transTm4 (Var ann name) _             = do
  (Normalized ty) <- lookupVarM name
  return  (ty, (BiVar () (void name)))

transTm4 (TyAbs ann n k tm) mode = do
  let k' = void k
  (ty, tmBi) <- withTyVar n k' (transTm4 tm mode)
  let ty'  = TyForall () (void n) k' ty
  return (ty', tmBi)
    
transTm4 (LamAbs ann n dom body) mode = do
  (Normalized vDom) <- normalizeTypeOptM $ void dom
  (cDom, biBody) <- withVar n (Normalized vDom) (transTm4 body Check)
  let ty    = TyFun () vDom cDom
      biTm' = BiLamAbs () (void n) biBody
      biTm  = case mode of
        Synth -> TyAnn () biTm' ty
        Check -> biTm'
      in return (ty, biTm)
      
transTm4 (Apply ann fun arg)     mode = do
  (funTy, biFun) <- transTm4 fun Check
  (argTy, biArg) <- transTm4 arg Synth
  let (TyFun _ _ cod) = funTy
      biTm = case mode of
               Synth -> TyAnn () (BiApply () biFun biArg) cod
               Check -> BiApply () biFun biArg
      in return (cod, biTm)

transTm4 (Constant ann con)      _    = do
  let Normalized ty = typeOfConstant con
  return (ty, (BiConstant () (void con)))

transTm4 (Builtin ann b)         _    = do
  Normalized ty <- inferTypeOfBuiltinM b
  return (ty, BiBuiltin () (void b))

transTm4 (TyInst ann tm ty)      mode = do
  (biTy, biTm) <- transTm4 tm mode
  case biTy of
    TyForall ann' n nk vCod -> do
      vTy <- normalizeTypeOptM $ void ty
      Normalized nTy <- substNormalizeTypeM vTy n vCod
      return (nTy, biTm)

transTm4 (Unwrap ann tm)         mode = do
  -- type of Unwrap doesn't depend on tm
  -- so tm can't possibly be checked against checking mode type 
  (tmTy, biTm) <- transTm4 tm Synth
  Normalized ty <- case tmTy of
    TyIFix _ vPat vArg -> do
      k <- inferKindM $ ann <$ vArg
      unfoldFixOf (Normalized vPat) (Normalized vArg) k
    _                  -> throwError (TypeMismatch ann (void tm) (TyIFix () dummyType dummyType) (Normalized tmTy))
  case mode of
    Synth -> return (ty, TyAnn () (BiUnwrap () biTm) ty)
    Check -> return (ty, BiUnwrap () biTm)

transTm4 (IWrap ann pat arg tm)  mode = do
  Normalized vPat <- normalizeTypeOptM $ void pat
  Normalized vArg <- normalizeTypeOptM $ void arg
  -- type of IWrap doesn't depend on tm
  -- so tm can't possibly be checked against checking mode type 
  (ty, biTm) <- transTm4 tm Synth
  case mode of
    Synth -> return (ty, TyAnn () (BiIWrap () vPat vArg biTm) ty)
    Check -> return (ty, BiIWrap () vPat vArg biTm)
  
transTm4 (Error ann ty)          _    = do
  Normalized ty' <- normalizeTypeOptM $ void ty
  return (ty', BiError () ty')

-- ---------------------------------------------------------------------------

transProg :: Program TyName Name ()
          -> BiProgram TyName Name ()
transProg (Program ann version tm) = case transTmConcrete tm of
  Left e          -> error $ show e
  Right (_, biTm) -> BiProgram () (void version) biTm

transTmConcrete :: Term TyName Name ()
                -> Either (Error ())
                          ((Type TyName () ,
                            BiTerm TyName Name ()))
transTmConcrete tm = runQuoteT $ do
  bis <- getStringBuiltinTypes ()
  transType (biChainConfig { _tccDynamicBuiltinNameTypes = bis }) (nameHack tm)

transType config = rename >=> runTypeCheckM config . ((flip transTm) Synth) 

-- --------------------------------------------------------------------------------------

transProg2 :: Program TyName Name ()
           -> BiProgram TyName Name ()
transProg2 (Program ann version tm) = case transTmConcrete2 tm of
  Left e          -> undefined
  Right (_, biTm) -> BiProgram () (void version) biTm

transTmConcrete2 :: Term TyName Name ()
                 -> Either (Error ())
                           ((Type TyName () ,
                             BiTerm TyName Name ()))
transTmConcrete2 tm = runQuoteT $ do
  bis <- getStringBuiltinTypes ()
  transType2 (biChainConfig { _tccDynamicBuiltinNameTypes = bis }) tm

transType2 config = rename >=> runTypeCheckM config . ((flip transTm2) Synth) 

-- --------------------------------------------------------------------------------------

transProg3 :: Program TyName Name ()
           -> BiProgram TyName Name ()
transProg3 (Program ann version tm) = case transTmConcrete3 tm of
  Left e          -> undefined
  Right (_, biTm) -> BiProgram () (void version) biTm

transTmConcrete3 :: Term TyName Name ()
                 -> Either (Error ())
                           ((Type TyName () ,
                             BiTerm TyName Name ()))
transTmConcrete3 tm = runQuoteT $ do
  bis <- getStringBuiltinTypes ()
  transType3 (biChainConfig { _tccDynamicBuiltinNameTypes = bis }) tm

transType3 config = rename >=> runTypeCheckM config . ((flip transTm3) Synth) 

-- --------------------------------------------------------------------------------------

transProg4 :: Program TyName Name ()
           -> BiProgram TyName Name ()
transProg4 (Program ann version tm) = case transTmConcrete4 tm of
  Left e          -> undefined
  Right (_, biTm) -> BiProgram () (void version) biTm

transTmConcrete4 :: Term TyName Name ()
                 -> Either (Error ())
                           ((Type TyName () ,
                             BiTerm TyName Name ()))
transTmConcrete4 tm = runQuoteT $ do
  bis <- getStringBuiltinTypes ()
  transType4 (biChainConfig { _tccDynamicBuiltinNameTypes = bis }) tm

transType4 config = rename >=> runTypeCheckM config . ((flip transTm4) Synth) 

------------------------------------------------------------------------------------------
-- erased terms --------------------------------------------------------------------------
------------------------------------------------------------------------------------------

eTm :: BiTerm TyName Name ann -> ETerm Name ann
eTm (BiVar      ann name)         = EVar      ann name
eTm (BiLamAbs   ann name tm)      = ELamAbs   ann name (eTm tm)
eTm (BiApply    ann      tm1 tm2) = EApply    ann      (eTm tm1) (eTm tm2)
eTm (BiConstant ann      c)       = EConstant ann c
eTm (BiBuiltin  ann      b)       = EBuiltin  ann b
eTm (BiUnwrap   ann      tm)      = EUnwrap   ann (eTm tm)
eTm (BiIWrap    ann      _ _ tm)  = EIWrap    ann (eTm tm)
eTm (BiError    ann      _)       = EError    ann
eTm (TyAnn      ann      tm _)    = eTm tm

eProg :: BiProgram TyName Name ann -> EProgram Name ann
eProg (BiProgram ann version tm) = EProgram ann version (eTm tm)

eConcrete :: Program TyName Name ()
          -> EProgram Name ()
eConcrete (Program ann version tm) =
  let pr = case transTmConcrete4 tm of
             Left e          -> undefined
             Right (_, biTm) -> BiProgram () (void version) biTm
      in eProg pr

-------------------------------------------------------------------------------------------
-- nameless terms -------------------------------------------------------------------------
-------------------------------------------------------------------------------------------

deBruijnConcrete :: Program TyName Name ()
                 -> Program TyDeBruijn DeBruijn ()
deBruijnConcrete p =
  case deBruijnProgram p of
    Left e -> undefined
    Right db -> db

biChainConfig :: TypeCheckConfig
biChainConfig = TypeCheckConfig True mempty Nothing

-- give variables unique namestrings so they can be crossreferenced 
-- despite their Uniques being refreshed
nameHack :: Term TyName Name ann -> Term TyName Name ann
nameHack = termHack
  where termHack (Var ann n) = Var ann (nHack n)
        termHack (TyAbs ann n k tm) = TyAbs ann (tHack n) k (termHack tm)
        termHack (LamAbs ann n ty tm) = LamAbs ann (nHack n) (tyHack ty) (termHack tm)
        termHack (Apply ann tm1 tm2) = Apply ann (termHack tm1) (termHack tm2)
        termHack (Constant ann c) = Constant ann c
        termHack (Builtin ann b) = Builtin ann b
        termHack (TyInst ann tm ty) = TyInst ann (termHack tm) (tyHack ty)
        termHack (Unwrap ann tm) = Unwrap ann (termHack tm)
        termHack (IWrap ann ty1 ty2 tm) = IWrap ann (tyHack ty1) (tyHack ty2) (termHack tm)
        termHack (Error ann ty) = Error ann (tyHack ty)
        nHack :: Name ann -> Name ann
        nHack n = mapNameString (\s -> pack $ (unpack s) ++ "~" ++ (show $ unUnique $ nameUnique n)) n
        tHack :: TyName ann -> TyName ann
        tHack = TyName . nHack . unTyName
        tyHack :: Type TyName ann -> Type TyName ann
        tyHack (TyVar ann n) = TyVar ann (tHack n)
        tyHack (TyFun ann ty1 ty2) = TyFun ann (tyHack ty1) (tyHack ty2)
        tyHack (TyIFix ann ty1 ty2) = TyIFix ann (tyHack ty1) (tyHack ty2)
        tyHack (TyForall ann n k ty) = TyForall ann (tHack n) k (tyHack ty)
        tyHack (TyBuiltin ann tb) = TyBuiltin ann tb
        tyHack (TyLam ann n k ty) = TyLam ann (tHack n) k (tyHack ty)
        tyHack (TyApp ann ty1 ty2) = TyApp ann (tyHack ty1) (tyHack ty2)