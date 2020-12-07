{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE OverloadedStrings     #-}

module Language.PlutusCore.TypeCheck.Bi where

import PlutusPrelude
  
import Language.PlutusCore.Name
import Language.PlutusCore.Error

import Language.PlutusCore.Core.Type
import Language.PlutusCore.Core.BiType

import Language.PlutusCore.TypeCheck
import Language.PlutusCore.TypeCheck.Internal hiding (checkTypeM)

import Language.PlutusCore.Constant.Dynamic.OffChain

import Language.PlutusCore.Rename

import Language.PlutusCore.Quote

import Language.PlutusCore.DeBruijn

import Language.PlutusCore.Subst

import Language.PlutusCore.Normalize.Internal

import Language.PlutusCore.Mark
  
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Set as S

import Language.PlutusCore.MkPlc (mkIterTyApp)

import Debug.Trace
import Data.Text (unpack)
-- import qualified Data.DList as DL
  
data Mode = Check | Synth
  
synthTypeM :: BiTerm TyName Name () -> TypeCheckM () (Normalized (Type TyName ()))
synthTypeM tm | trace (show $ sizeTm tm) False = undefined
synthTypeM (BiConstant _ con)     = pure $ typeOfConstant con
synthTypeM (BiBuiltin _ bi)       = do 
  Normalized (ty,s) <- inferTypeOfBuiltinM' bi
  return $ Normalized ty
synthTypeM (BiVar _ name)         = lookupVarM name
synthTypeM (BiLamAbs _ n body)    = throwError $ Other "can't synthesize type for lambda"
synthTypeM (BiApply ann fun arg)  = do
  -- let !_ = traceShow ("Synth BiApply\n" ++ (dbShow (BiApply ann fun arg)) ++ "\n\n") False 
  ty <- synthTypeM fun
  case unNormalized ty of
    TyFun _ vDom vCod -> do
      checkTypeM arg $ Normalized vDom
      pure $ Normalized vCod
    _ -> throwError $ Other "synthesize: not an arrow type"
synthTypeM (BiIWrap _ pat arg tm)   = undefined -- unused for now
synthTypeM (BiUnwrap _ tm)          = undefined -- unused for now
synthTypeM (BiError ann ty)       = do
  checkKindM ann ty $ Type ()
  Normalized (ty',s) <- normalizeTypeOptM' $ void ty
  -- traceM $ show $ DL.map (\(x,y) -> (unUnique $ unTypeUnique x, unUnique $ unTypeUnique y)) s
  return $ Normalized ty'
synthTypeM (TyAnn _ tm ty)        = do
  -- let !_ = traceShow ("Synth Ann\n" ++ (dbShow (TyAnn () tm ty)) ++ "\n\n") False
  Normalized (nTy,s) <- normalizeTypeOptM' (void ty)
  -- traceM $ show $ S.map (\(x,y) -> (unUnique $ unTypeUnique x, unUnique $ unTypeUnique y)) s
  k <- inferKindM nTy
  when (k /= (Type ())) $ throwError $ Other "annotation has wrong kind"
  let bv = getBoundVars nTy
  -- traceM $ "binding: " ++ show bv
  withTyVars (getBoundVars nTy) (checkTypeM tm (Normalized nTy))
  return (Normalized nTy)

withTyVars :: [(TyName ann, Kind ())] -> TypeCheckM ann a -> TypeCheckM ann a
withTyVars [] c = c
withTyVars ((n,k):nks) c = withTyVar n k (withTyVars nks c)

getBoundVars :: Type TyName ann -> [(TyName ann, Kind ann)]
getBoundVars (TyVar _ _) = []
getBoundVars (TyFun _ ty1 ty2) = (getBoundVars ty1) ++ (getBoundVars ty2)
getBoundVars (TyIFix _ ty1 ty2) = (getBoundVars ty1) ++ (getBoundVars ty2)
getBoundVars (TyForall _ n k ty) = (n,k) : (getBoundVars ty)
getBoundVars (TyBuiltin _ _) = []
getBoundVars (TyLam _ n k ty) = (n,k) : (getBoundVars ty)
getBoundVars (TyApp _ ty1 ty2) = (getBoundVars ty1) ++ (getBoundVars ty2)

checkTypeM :: BiTerm TyName Name () -> Normalized (Type TyName ()) -> TypeCheckM () ()
checkTypeM tm _ | trace (show $ sizeTm tm) False = undefined
checkTypeM tm (Normalized (TyForall _ n k ty))     = do
  -- TODO check kind
  -- let !_ = traceShow ("Check ForAll\n" ++ (dbShow tm) ++ "\n\n") False
  {-withTyVar n k -} 
  (checkTypeM tm (Normalized ty))
checkTypeM tm@(BiLamAbs _ n body)  ty
  | Normalized (TyFun _ dom cdom) <- ty = --traceM ("Check Lambda (fun)\n" ++ (dbShow tm)) >>
      withVar n (Normalized dom) (checkTypeM body $ Normalized cdom)
  | Normalized (TyIFix _ pat arg) <- ty = do
      -- let !_ = traceShow ("Check Lambda (fix)\n" ++ (dbShow tm) ++ "\n\n") False
      k <- inferKindM arg
      Normalized (ty',s) <- unfoldFixOf' (Normalized pat) (Normalized arg) k
      -- traceM $ show $ S.map (\(x,y) -> (unUnique $ unTypeUnique x, unUnique $ unTypeUnique y)) s
      checkTypeM tm (Normalized ty')
checkTypeM tm ty = do
  -- let !_ = traceShow ("Check (fallthrough)\n" ++ (dbShow tm) ++ "\n\n") False
  Normalized ty' <- synthTypeM tm
  case ty' of
    (TyForall _ n k _) -> unify (ftvTy $ unNormalized ty) (unNormalized ty :~: skipForall ty')
    _                  -> do
      b <- normAlphaEq ty (Normalized ty')
      when (not b) $ throwError $ Other $
        "checking failed: "
        ++ show (unNormalized ty) ++ "###############"
        ++ show ty' ++ "##############"
        ++ show tm
{-
checkTypeM tm@(BiConstant _ _)     ty = do
  vTy <- synthTypeM tm
  when (normAlphaEq ty vTy) $ throwError $ Other $ "checking failed: constant\n" ++ show ty ++ "\n\n" ++ show vTy
checkTypeM tm@(BiBuiltin _ _)      ty = do
  vTy <- synthTypeM tm
  when (normAlphaEq ty vTy) $ throwError $ Other $ "checking failed: builtin\n" ++ show ty ++ "\n\n" ++ show vTy
checkTypeM tm@(BiVar _ _)          ty = do
  vTy <- synthTypeM tm
  when (normAlphaEq ty vTy) $ throwError $ Other $ "checking failed: variable: \n" ++ show ty ++ "\n\n" ++ show vTy
checkTypeM tm@(BiApply _ _ _)      ty = do
  vTy <- synthTypeM tm
  when (normAlphaEq ty vTy) $ throwError $ Other $ "checking failed: application: \n" ++ show ty ++ "\n\n" ++ show vTy
checkTypeM    (BiIWrap _ pat arg tm) ty = undefined -- unused for now
checkTypeM    (BiUnwrap _ tm)        ty = undefined -- unused for now
checkTypeM    (BiError ann ty')      ty = do
  when (normAlphaEq ty  (Normalized ty')) $ throwError $ Other $ "checking failed: error term\n" ++ show ty ++ "\n\n" ++ show ty'
-- checkTypeM    (TyAnn _ tm ty')      ty = throwError $ Other $ "encountered annotation in checking mode: \n" ++ show ty' ++ "\n\n" ++ show ty
-}
skipForall :: Type TyName ann -> Type TyName ann
skipForall (TyForall _ _ _ ty) = skipForall ty
skipForall ty                  = ty

-- hecco :: Normalized (Type TyName ()) -> Normalized (Type TyName ()) -> Bool
-- hecco (Normalized (TyVar _ n1)) (Normalized (TyVar _ n2)) = nameString (unTyName n1) /= nameString (unTyName n2)
-- hecco t1 t2 = t1 /= t2

normAlphaEq :: Normalized (Type TyName ()) -> Normalized (Type TyName ()) -> TypeCheckM () Bool
normAlphaEq (Normalized ty1) (Normalized ty2) = alphaEq ty1 ty2 >>= pure
  
alphaEq :: Type TyName () -> Type TyName () -> TypeCheckM () Bool
alphaEq (TyForall _ n1 k1 ty1) (TyForall _ n2 k2 ty2)
          | k1 == k2 = alphaEq ty1 (sub1 n2 (TyVar () n1) ty2)
alphaEq (TyLam _ n1 k1 ty1) (TyLam _ n2 k2 ty2)
          | k1 == k2 = alphaEq ty1 (sub1 n2 (TyVar () n1) ty2)
alphaEq (TyFun _ ty1 ty1')  (TyFun _ ty2 ty2')  = do
  b1 <- alphaEq ty1 ty2
  b2 <- alphaEq ty1' ty2'
  pure $ b1 && b2
alphaEq (TyApp _ ty1 ty1')  (TyApp _ ty2 ty2')  = do
  b1 <- alphaEq ty1 ty2
  b2 <- alphaEq ty1' ty2'
  pure $ b1 && b2
alphaEq (TyIFix _ ty1 ty1') (TyIFix _ ty2 ty2') = do
  b1 <- alphaEq ty1 ty2
  b2 <- alphaEq ty1' ty2'
  pure $ b1 && b2
alphaEq (TyBuiltin _ b1)    (TyBuiltin _ b2)    = pure $ b1 == b2
alphaEq (TyVar _ n1)        (TyVar _ n2)        = pure $ nameString (unTyName n1) == nameString (unTyName n2)
alphaEq (TyIFix _ pat arg) ty                   = do
  k <- inferKindM arg
  Normalized ty' <- unfoldFixOf (Normalized pat) (Normalized arg) k
  alphaEq ty ty'
alphaEq ty (TyIFix _ pat arg)                   = do
  k <- inferKindM arg
  Normalized ty' <- unfoldFixOf (Normalized pat) (Normalized arg) k
  alphaEq ty ty'
alphaEq _                   _                   = pure $ False
 
data EqCt ann = Type TyName ann :~: Type TyName ann
type EqCs ann = [EqCt ann]

unify :: MonadError (TypeError ()) m => S.Set (TyName ()) -> EqCt () -> m ()
unify us eq = runQuoteT $ go us [eq]
  where go :: MonadError (TypeError ()) m => S.Set (TyName ()) -> EqCs () -> QuoteT m ()
        go _  [] = pure ()
        go us ((TyVar _ n1 :~: TyVar _ n2):xs)
          | (nameString $ unTyName n1) == (nameString $ unTyName n2) = go us xs
        go us ((TyVar _ n :~: ty):xs)
          | n `S.notMember` us
          , occursCheck n ty = go us $ subst n ty xs
        go us ((ty :~: TyVar _ n):xs)
          | n `S.notMember` us
          , occursCheck n ty = go us $ subst n ty xs
        go us ((TyForall _ n1 k1 ty1 :~: TyForall _ n2 k2 ty2):xs)
          | k1 == k2 = do
              (n1', ty1') <- refresh n1 ty1
              (n2', ty2') <- refresh n2 ty2
              go us $ (TyVar () n1' :~: TyVar () n2'):(ty1' :~: ty2'):xs
        go us ((TyLam _ n1 k1 ty1 :~: TyLam _ n2 k2 ty2):xs)
          | k1 == k2 = do
              (n1', ty1') <- refresh n1 ty1
              (n2', ty2') <- refresh n2 ty2
              go us $ (TyVar () n1' :~: TyVar () n2'):(ty1' :~: ty2'):xs
        go us ((TyBuiltin _ b1 :~: TyBuiltin _ b2):xs)
          | b1 == b2 = go us xs
        go us ((TyFun _ ty1 ty2 :~: TyFun _ ty3 ty4):xs) =
          go us $ (ty1 :~: ty3):(ty2 :~: ty4):xs
        go us ((TyApp _ ty1 ty2 :~: TyApp _ ty3 ty4):xs) =
          go us $ (ty1 :~: ty3):(ty2 :~: ty4):xs
        go us ((TyIFix _ ty1 ty2 :~: TyIFix _ ty3 ty4):xs) =
          go us $ (ty1 :~: ty3):(ty2 :~: ty4):xs
        go _ ((ty1 :~: ty2):xs) = throwError $ Other $ "unification failed: " ++ show ty1 ++ "\n\n" ++ show ty2

-- | replace n with ty in cs, not substituting under binders
subst :: TyName ann -> Type TyName ann -> EqCs ann -> EqCs ann
subst n ty cs = map (both (sub1 n ty)) cs
  where both :: (Type TyName ann -> Type TyName ann) -> EqCt ann -> EqCt ann
        both f (t1 :~: t2) = (f t1 :~: f t2)

sub1 :: TyName ann -> Type TyName ann -> Type TyName ann -> Type TyName ann
sub1 n t t' = typeSubstTyNames (\n' -> if
                                | n == n'   -> Just t
                                | otherwise -> Nothing) t' 

-- | freshen the top-level bound variable
refresh :: Monad m => TyName () -> Type TyName () -> QuoteT m (TyName (), Type TyName ())
refresh n t = freshenTyName n >>= \n' -> pure (n', sub1 n (TyVar () n') t)

-- | Check that the variable doesn't occur free in the type
occursCheck :: TyName ann -> Type TyName ann -> Bool
occursCheck n (TyVar _ n')        = n /= n'
occursCheck n (TyForall _ n' _ t) = n == n' || occursCheck n t
occursCheck n (TyLam    _ n' _ t) = n == n' || occursCheck n t
occursCheck n (TyFun    _ t1 t2)  = occursCheck n t1 && occursCheck n t2
occursCheck n (TyApp    _ t1 t2)  = occursCheck n t1 && occursCheck n t2
occursCheck n (TyIFix   _ t1 t2)  = occursCheck n t1 && occursCheck n t2
occursCheck _ (TyBuiltin _ _)     = True

concrete :: BiTerm TyName Name ()
                 -> Either (Error ())
                           (Normalized (Type TyName ()))
concrete tm = runQuoteT $ do
  bis <- getStringBuiltinTypes ()
  let config = biChainConfig { _tccDynamicBuiltinNameTypes = bis }
  (rename >=> runTypeCheckM config . synthTypeM) tm
  
biChainConfig :: TypeCheckConfig
biChainConfig = TypeCheckConfig True mempty Nothing

typeCheckTerm :: BiTerm TyName Name () -> Type TyName ()
typeCheckTerm tm = case concrete tm of
                     Left e   -> error $ show e
                     Right ty -> unNormalized ty

typeCheck :: BiProgram TyName Name () -> Type TyName ()
typeCheck p = typeCheckTerm $ toTerm p

dbShow :: BiTerm TyName Name () -> String
dbShow = s
  where s :: BiTerm TyName Name () -> String
        s (BiVar _ n) = sn n
        s (BiLamAbs _ n tm) = "( \\ " ++ sn n ++ ". " ++ s tm ++ ")"
        s (BiApply _ fun arg) = "(App " ++ s fun ++ " #> " ++ s arg ++ ")"
        s (BiConstant _ c) = "(Const " ++ show c ++ ")"
        s (BiBuiltin _ b) = "(Bltin " ++ show b ++ ")"
        s (BiUnwrap _ tm) = "(Unwrap " ++ s tm ++ ")"
        s (BiIWrap _ ty1 ty2 tm) = "(IWrap " ++ t ty1 ++ " @> " ++ t ty2 ++ ")"
        s (BiError _ ty) = "(Error " ++ t ty ++ ")"
        s (TyAnn _ tm ty) = "(Ann " ++ s tm ++ " ;; " ++ t ty ++ ")" 
        t :: Type TyName () -> String
        t = dbShowTy
        sn :: Name () -> String
        sn n = (unpack $ nameString n) ++ "_" ++ (show $ unUnique $ nameUnique n)

dbShowTy :: Type TyName () -> String
dbShowTy = t
  where t :: Type TyName () -> String
        t (TyVar _ n) = tn n
        t (TyFun _ arg res) = "(" ++ t arg ++ " -> " ++ t res ++ ")"
        t (TyIFix _ ty1 ty2) = "(IFix " ++ t ty1 ++ " @@ " ++ t ty2 ++ ")"
        t (TyForall _ n k ty) = "(\\/ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (TyBuiltin _ n) = "(TBtin " ++ show n ++ ")"
        t (TyLam _ n k ty) = "( /\\ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (TyApp _ fun arg) = "(TApp " ++ t fun ++ " ## " ++ t arg ++ ")" 
        tn :: TyName () -> String
        tn n' = let n = unTyName n' in ((unpack $ nameString n) ++ "_" ++ (show $ unUnique $ nameUnique n))

normalizeTypeOptM' :: Type TyName () -> TypeCheckM ann (Normalized (Type TyName (), S.Set (TypeUnique, TypeUnique)))
normalizeTypeOptM' ty = do
    normTypes <- pure True
    if normTypes
        then runNormalizeTypeFullM $ normalizeTypeM' ty
        else pure $ Normalized (ty, S.empty)

inferTypeOfBuiltinM' :: Builtin ann -> TypeCheckM ann (Normalized (Type TyName (), S.Set (TypeUnique, TypeUnique)))
-- We have a weird corner case here: the type of a 'BuiltinName' can contain 'TypedBuiltinDyn', i.e.
-- a static built-in name is allowed to depend on a dynamic built-in type which are not required
-- to be normalized. For dynamic built-in names we store a map from them to their *normalized types*,
-- with the normalization happening in this module, but what should we do for static built-in names?
-- Right now we just renormalize the type of a static built-in name each time we encounter that name.
inferTypeOfBuiltinM' (BuiltinName    _   name) = runNormalizeTypeFullM $ normalizeTypeM' $ typeOfBuiltinName name
-- TODO: inline this definition once we have only dynamic built-in names.
inferTypeOfBuiltinM' bi@(DynBuiltinName ann name) = do
  Normalized ty <- inferTypeOfBuiltinM bi
  pure $ Normalized (ty, S.empty)

unfoldFixOf'
    :: Normalized (Type TyName ())  -- ^ @vPat@
    -> Normalized (Type TyName ())  -- ^ @vArg@
    -> Kind ()                      -- ^ @k@
    -> TypeCheckM ann (Normalized (Type TyName (), S.Set (TypeUnique, TypeUnique)))
unfoldFixOf' pat arg k = do
    let vPat = unNormalized pat
        vArg = unNormalized arg
    traceM $ "unfolding:\n" ++ dbShowTy vPat ++ "\n\n" ++ dbShowTy vArg ++ "\n\n\n"
    a <- liftQuote $ freshTyName () "a"
    runNormalizeTypeFullM $ normalizeTypeM' $
        mkIterTyApp () vPat
            [ TyLam () a k . TyIFix () vPat $ TyVar () a
            , vArg
            ]

sizeTm :: BiTerm tyname name ann -> Int
sizeTm (BiVar _ n) = 1
sizeTm (BiLamAbs _ n tm) = 1 + sizeTm tm
sizeTm (BiApply _ fun arg) = 1 + sizeTm fun + sizeTm arg
sizeTm (BiConstant _ c) = 1
sizeTm (BiBuiltin _ b) = 1
sizeTm (BiUnwrap _ tm) = 1 + sizeTm tm
sizeTm (BiIWrap _ ty1 ty2 tm) = 1 + sizeTm tm
sizeTm (BiError _ ty) = 1
sizeTm (TyAnn _ tm ty) = 1 + sizeTm tm 