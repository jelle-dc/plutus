-- | The internal module of the renamer that defines the actual algorithms,
-- but not the user-facing API.

module Language.PlutusCore.Rename.Internal
    ( module Export
    , withFreshenedTyVarDecl
    , withFreshenedVarDecl
    , renameTypeM
    , renameTypeM'
    , renameTermM
    , renameBiTermM
    , renameProgramM
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename.Monad as Export

import Data.Set
import Control.Monad.Trans.Writer.CPS
import Control.Monad.Trans

import Data.Text (unpack)

import Debug.Trace

import           Control.Lens

-- | Replace the unique in the name stored in a 'TyVarDecl' by a new unique, save the mapping
-- from the old unique to the new one and supply the updated 'TyVarDecl' to a continuation.
withFreshenedTyVarDecl
    :: (HasRenaming ren TypeUnique, HasUniques (Type tyname ann), MonadQuote m)
    => TyVarDecl tyname ann
    -> (TyVarDecl tyname ann -> RenameT ren m c)
    -> RenameT ren m c
withFreshenedTyVarDecl (TyVarDecl ann name kind) cont =
    withFreshenedName name $ \nameFr -> cont $ TyVarDecl ann nameFr kind

-- | Replace the unique in the name stored in a 'VarDecl' by a new unique, save the mapping
-- from the old unique to the new one and supply to a continuation the computation that
-- renames the type stored in the updated 'VarDecl'.
-- The reason the continuation receives a computation rather than a pure term is that we may want
-- to bring several term and type variables in scope before renaming the types of term variables.
-- This situation arises when we want to rename a bunch of mutually recursive bindings.
withFreshenedVarDecl
    :: (HasUniques (Term tyname name ann), MonadQuote m)
    => VarDecl tyname name ann
    -> (ScopedRenameT m (VarDecl tyname name ann) -> ScopedRenameT m c)
    -> ScopedRenameT m c
withFreshenedVarDecl (VarDecl ann name ty) cont =
    withFreshenedName name $ \nameFr -> cont $ VarDecl ann nameFr <$> renameTypeM ty

-- | Rename a 'Type' in the 'RenameM' monad.
renameTypeM
    :: (HasRenaming ren TypeUnique, HasUniques (Type tyname ann), MonadQuote m)
    => Type tyname ann -> RenameT ren m (Type tyname ann)
renameTypeM (TyLam ann name kind ty)    =
    withFreshenedName name $ \nameFr -> TyLam ann nameFr kind <$> renameTypeM ty
renameTypeM (TyForall ann name kind ty) =
    withFreshenedName name $ \nameFr -> TyForall ann nameFr kind <$> renameTypeM ty
renameTypeM (TyIFix ann pat arg)        = TyIFix ann <$> renameTypeM pat <*> renameTypeM arg
renameTypeM (TyApp ann fun arg)         = TyApp ann <$> renameTypeM fun <*> renameTypeM arg
renameTypeM (TyFun ann dom cod)         = TyFun ann <$> renameTypeM dom <*> renameTypeM cod
renameTypeM (TyVar ann name)            = TyVar ann <$> renameNameM name
renameTypeM ty@TyBuiltin{}              = pure ty

renameTypeM'
    :: (HasRenaming ren TypeUnique, HasUniques (Type tyname ann), MonadQuote m)
    => Type tyname ann -> WriterT (Set (TypeUnique, TypeUnique)) (RenameT ren m) (Type tyname ann)
renameTypeM' (TyLam ann name kind ty)    = do
    ty' <- renameTypeM' ty
    withFreshenedName' name $ \nameFr -> pure $ TyLam ann nameFr kind ty'
renameTypeM' (TyForall ann name kind ty) = do
    ty' <- renameTypeM' ty
    withFreshenedName' name $ \nameFr -> pure $ TyForall ann nameFr kind ty'
renameTypeM' (TyIFix ann pat arg)        = do
    pat' <- renameTypeM' pat
    arg' <- renameTypeM' arg
    return $ TyIFix ann pat' arg'
renameTypeM' (TyApp ann fun arg)         = do
    fun' <- renameTypeM' fun
    arg' <- renameTypeM' arg
    return $ TyApp ann fun' arg'
renameTypeM' (TyFun ann dom cod)         = do
    dom' <- renameTypeM' dom
    cod' <- renameTypeM' cod
    return $ TyFun ann dom' cod'
renameTypeM' (TyVar ann name)            = lift $ TyVar ann <$> renameNameM name
renameTypeM' ty@TyBuiltin{}              = pure ty

-- | Rename a 'Term' in the 'RenameM' monad.
renameTermM
    :: (HasUniques (Term tyname name ann), MonadQuote m)
    => Term tyname name ann -> ScopedRenameT m (Term tyname name ann)
renameTermM (LamAbs ann name ty body)  =
    withFreshenedName name $ \nameFr -> LamAbs ann nameFr <$> renameTypeM ty <*> renameTermM body
renameTermM (TyAbs ann name kind body) =
    withFreshenedName name $ \nameFr -> TyAbs ann nameFr kind <$> renameTermM body
renameTermM (IWrap ann pat arg term)   =
    IWrap ann <$> renameTypeM pat <*> renameTypeM arg <*> renameTermM term
renameTermM (Apply ann fun arg)        = Apply ann <$> renameTermM fun <*> renameTermM arg
renameTermM (Unwrap ann term)          = Unwrap ann <$> renameTermM term
renameTermM (Error ann ty)             = Error ann <$> renameTypeM ty
renameTermM (TyInst ann term ty)       = TyInst ann <$> renameTermM term <*> renameTypeM ty
renameTermM (Var ann name)             = Var ann <$> renameNameM name
renameTermM con@Constant{}             = pure con
renameTermM bi@Builtin{}               = pure bi

-- | Rename a 'BiTerm' in the 'RenameM' monad.
renameBiTermM
    :: (HasUniques (BiTerm tyname name ann), MonadQuote m)
    => BiTerm tyname name ann -> ScopedRenameT m (BiTerm tyname name ann)
renameBiTermM (BiLamAbs ann name body)  =
    withFreshenedName name $ \nameFr -> BiLamAbs ann nameFr <$> renameBiTermM body
renameBiTermM (BiIWrap ann pat arg term)   = traceM "god fucking dammit" >>
    BiIWrap ann <$> renameTypeM pat <*> renameTypeM arg <*> renameBiTermM term
renameBiTermM (BiApply ann fun arg)        = BiApply ann <$> renameBiTermM fun <*> renameBiTermM arg
renameBiTermM (BiUnwrap ann term)          = BiUnwrap ann <$> renameBiTermM term
renameBiTermM (BiError ann ty)             = BiError ann <$> renameTypeM ty
renameBiTermM (BiVar ann name)             = BiVar ann <$> renameNameM name
renameBiTermM con@BiConstant{}             = pure con
renameBiTermM bi@BiBuiltin{}               = pure bi
renameBiTermM (TyAnn ann tm ty@(TyFun _ _ _)) = do
    traceM $ "\n\n\nentering: " ++ dbShowTy ty
    (ty', tm') <- addNames ty tm
    pure $ TyAnn ann tm' ty'
  where addNames tz@(TyForall ann' n k ty) tm = withFreshenedName n $ \n' -> do
          traceM $ "entering forall: " ++ dbShowTy tz
          (ty', tm') <- addNames ty tm
          traceM $ "exiting forall: " ++ dbShowTy tz
          let ty = (TyForall ann' n' k ty')
          pure (ty, tm')
        addNames tz@(TyFun ann' ty1 ty2) tm = do
            traceM $ "entering fun: " ++ dbShowTy tz
            (ty1', tm') <- addNames ty1 tm
            traceM $ "exiting fun1: " ++ dbShowTy tz
            (ty2', tm'') <- addNames ty2 tm'
            traceM $ "exiting fun2: " ++ dbShowTy tz
            let ty = TyFun ann' ty1' ty2'
            pure (ty, tm'')
        addNames ty tm = do ty' <- renameTypeM ty
                            tm' <- renameBiTermM tm
                            pure (ty', tm')
renameBiTermM (TyAnn ann tm ty@(TyForall _ _ _ _)) = do 
    traceM $ "\n\n\nentering: " ++ dbShowTy ty
    (ty', tm') <- addNames ty tm
    pure $ TyAnn ann tm' ty'
  where addNames tz@(TyForall ann' n k ty) tm = withFreshenedName n $ \n' -> do
          traceM $ "entering forall: " ++ dbShowTy tz
          (ty', tm') <- addNames ty tm
          traceM $ "exiting forall: " ++ dbShowTy tz
          let ty = (TyForall ann' n' k ty')
          pure (ty, tm')
        addNames tz@(TyFun ann' ty1 ty2) tm = do
            traceM $ "entering fun: " ++ dbShowTy tz
            (ty1', tm') <- addNames ty1 tm
            traceM $ "exiting fun1: " ++ dbShowTy tz
            (ty2', tm'') <- addNames ty2 tm'
            traceM $ "exiting fun2: " ++ dbShowTy tz
            let ty = TyFun ann' ty1' ty2'
            pure (ty, tm'')
        addNames ty tm = do ty' <- renameTypeM ty
                            tm' <- renameBiTermM tm
                            pure (ty', tm')
--   where addNames (TyForall ann' n k ty) tm = withFreshenedName n $ \n' -> do
        --   (ty', tm') <- addNames ty tm
        --   let ty = (TyForall ann' n' k ty')
        --   pure (ty, tm')
        -- addNames ty tm = do ty' <- renameTypeM ty
                            -- tm' <- renameBiTermM tm
                            -- pure (ty', tm')
renameBiTermM (TyAnn ann tm ty)            = TyAnn ann <$> renameBiTermM tm <*> renameTypeM ty

-- | Rename a 'Program' in the 'RenameM' monad.
renameProgramM
    :: (HasUniques (Program tyname name ann), MonadQuote m)
    => Program tyname name ann -> ScopedRenameT m (Program tyname name ann)
renameProgramM (Program ann ver term) = Program ann ver <$> renameTermM term

dbShowTy :: HasUnique (tyname ann) TypeUnique => Type tyname ann -> String
dbShowTy = t
  where t :: HasUnique (tyname ann) TypeUnique => Type tyname ann -> String
        t (TyVar _ n) = tn n
        t (TyFun _ arg res) = "(" ++ t arg ++ " -> " ++ t res ++ ")"
        t (TyIFix _ ty1 ty2) = "(IFix " ++ t ty1 ++ " @@ " ++ t ty2 ++ ")"
        t (TyForall _ n k ty) = "(\\/ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (TyBuiltin _ n) = "(TBtin " ++ show n ++ ")"
        t (TyLam _ n k ty) = "( /\\ " ++ tn n ++ ". " ++ t ty ++ ")"
        t (TyApp _ fun arg) = "(TApp " ++ t fun ++ " ## " ++ t arg ++ ")" 
        tn :: HasUnique (tyname ann) TypeUnique => tyname ann -> String
        tn n = show $ unUnique $ unTypeUnique $ n ^. unique
