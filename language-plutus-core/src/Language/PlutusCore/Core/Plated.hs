{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.Core.Plated
    ( typeTyBinds
    , typeTyVars
    , typeUniques
    , typeSubtypes
    , typeSubtypesDeep
    , termTyBinds
    , termBinds
    , termVars
    , termUniques
    , termSubtypes
    , termSubtypesDeep
    , termSubterms
    , termSubtermsDeep
    , typeUniquesDeep
    , termUniquesDeep
    , biTermUniquesDeep
    ) where

import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Core.BiType
import           Language.PlutusCore.Name

import           Control.Lens

infixr 6 <^>

-- | Compose two folds to make them run in parallel. The results are concatenated.
(<^>) :: Fold s a -> Fold s a -> Fold s a
(f1 <^> f2) g s = f1 g s *> f2 g s

-- | Get all the direct child 'tyname a's of the given 'Type' from binders.
typeTyBinds :: Traversal' (Type tyname ann) (tyname ann)
typeTyBinds f = \case
    TyForall ann tn k ty -> f tn <&> \tn' -> TyForall ann tn' k ty
    TyLam ann tn k ty -> f tn <&> \tn' -> TyLam ann tn' k ty
    x -> pure x

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname ann) (tyname ann)
typeTyVars f = \case
    TyVar ann n -> TyVar ann <$> f n
    x -> pure x

-- | Get all the direct child 'Unique's of the given 'Type' from binders 'TyVar's.
typeUniques :: HasUniques (Type tyname ann) => Traversal' (Type tyname ann) Unique
typeUniques f = \case
    TyForall ann tn k ty -> theUnique f tn <&> \tn' -> TyForall ann tn' k ty
    TyLam ann tn k ty -> theUnique f tn <&> \tn' -> TyLam ann tn' k ty
    TyVar ann n -> theUnique f n <&> TyVar ann
    x -> pure x

{-# INLINE typeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname ann) (Type tyname ann)
typeSubtypes f = \case
    TyFun ann ty1 ty2 -> TyFun ann <$> f ty1 <*> f ty2
    TyIFix ann pat arg -> TyIFix ann <$> f pat <*> f arg
    TyForall ann tn k ty -> TyForall ann tn k <$> f ty
    TyLam ann tn k ty -> TyLam ann tn k <$> f ty
    TyApp ann ty1 ty2 -> TyApp ann <$> f ty1 <*> f ty2
    b@TyBuiltin {} -> pure b
    v@TyVar {} -> pure v

-- | Get all the transitive child 'Type's of the given 'Type'.
typeSubtypesDeep :: Fold (Type tyname ann) (Type tyname ann)
typeSubtypesDeep = cosmosOf typeSubtypes

-- | Get all the direct child 'tyname a's of the given 'Term' from 'TyAbs'es.
termTyBinds :: Traversal' (Term tyname name ann) (tyname ann)
termTyBinds f = \case
    TyAbs ann tn k t -> f tn <&> \tn' -> TyAbs ann tn' k t
    x -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'LamAbs'es.
termBinds :: Traversal' (Term tyname name ann) (name ann)
termBinds f = \case
    LamAbs ann n ty t -> f n <&> \n' -> LamAbs ann n' ty t
    x -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name ann) (name ann)
termVars f = \case
    Var ann n -> Var ann <$> f n
    x -> pure x

-- | Get all the direct child 'Unique's of the given 'Term' (including the type-level ones).
termUniques :: HasUniques (Term tyname name ann) => Traversal' (Term tyname name ann) Unique
termUniques f = \case
    TyAbs ann tn k t -> theUnique f tn <&> \tn' -> TyAbs ann tn' k t
    LamAbs ann n ty t -> theUnique f n <&> \n' -> LamAbs ann n' ty t
    Var ann n -> theUnique f n <&> Var ann
    x -> pure x

-- | Get all the direct child 'Unique's of the given 'Term' (including the type-level ones).
biTermUniques :: HasUniques (BiTerm tyname name ann) => Traversal' (BiTerm tyname name ann) Unique
biTermUniques f = \case
    -- get tyvars from annotation ???
    BiLamAbs ann n t -> theUnique f n <&> \n' -> BiLamAbs ann n' t
    BiVar ann n -> theUnique f n <&> BiVar ann
    x -> pure x

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term'.
termSubtypes :: Traversal' (Term tyname name ann) (Type tyname ann)
termSubtypes f = \case
    LamAbs ann n ty t -> LamAbs ann n <$> f ty <*> pure t
    TyInst ann t ty -> TyInst ann t <$> f ty
    IWrap ann ty1 ty2 t -> IWrap ann <$> f ty1 <*> f ty2 <*> pure t
    Error ann ty -> Error ann <$> f ty
    t@TyAbs {} -> pure t
    a@Apply {} -> pure a
    u@Unwrap {} -> pure u
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

{-# INLINE biTermSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term'.
biTermSubtypes :: Traversal' (BiTerm tyname name ann) (Type tyname ann)
biTermSubtypes f = \case
    BiIWrap ann ty1 ty2 t -> BiIWrap ann <$> f ty1 <*> f ty2 <*> pure t
    BiError ann ty -> BiError ann <$> f ty
    l@BiLamAbs {} -> pure l
    a@BiApply {} -> pure a
    u@BiUnwrap {} -> pure u
    v@BiVar {} -> pure v
    c@BiConstant {} -> pure c
    b@BiBuiltin {} -> pure b
    TyAnn ann t ty -> TyAnn ann t <$> f ty

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep :: Fold (Term tyname name ann) (Type tyname ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name ann) (Term tyname name ann)
termSubterms f = \case
    LamAbs ann n ty t -> LamAbs ann n ty <$> f t
    TyInst ann t ty -> TyInst ann <$> f t <*> pure ty
    IWrap ann ty1 ty2 t -> IWrap ann ty1 ty2 <$> f t
    TyAbs ann n k t -> TyAbs ann n k <$> f t
    Apply ann t1 t2 -> Apply ann <$> f t1 <*> f t2
    Unwrap ann t -> Unwrap ann <$> f t
    e@Error {} -> pure e
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

{-# INLINE biTermSubterms #-}
biTermSubterms :: Traversal' (BiTerm tyname name ann) (BiTerm tyname name ann)
biTermSubterms f = \case
    BiLamAbs ann n t -> BiLamAbs ann n <$> f t
    BiIWrap ann ty1 ty2 t -> BiIWrap ann ty1 ty2 <$> f t
    BiApply ann t1 t2 -> BiApply ann <$> f t1 <*> f t2
    BiUnwrap ann t -> BiUnwrap ann <$> f t
    e@BiError {} -> pure e
    v@BiVar {} -> pure v
    c@BiConstant {} -> pure c
    b@BiBuiltin {} -> pure b
    TyAnn ann t ty -> TyAnn ann <$> f t <*> pure ty

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term tyname name ann) (Term tyname name ann)
termSubtermsDeep = cosmosOf termSubterms

-- | Get all the transitive child 'Term's of the given 'Term'.
biTermSubtermsDeep :: Fold (BiTerm tyname name ann) (BiTerm tyname name ann)
biTermSubtermsDeep = cosmosOf biTermSubterms

-- | Get all the transitive child 'Unique's of the given 'Type'.
typeUniquesDeep :: HasUniques (Type tyname ann) => Fold (Type tyname ann) Unique
typeUniquesDeep = typeSubtypesDeep . typeUniques

-- | Get all the transitive child 'Unique's of the given 'Term' (including the type-level ones).
termUniquesDeep :: HasUniques (Term tyname name ann) => Fold (Term tyname name ann) Unique
termUniquesDeep = termSubtermsDeep . (termSubtypes . typeUniquesDeep <^> termUniques)

-- | Get all the transitive child 'Unique's of the given 'Term' (including the type-level ones).
biTermUniquesDeep :: HasUniques (BiTerm tyname name ann) => Fold (BiTerm tyname name ann) Unique
biTermUniquesDeep = biTermSubtermsDeep . (biTermSubtypes . typeUniquesDeep <^> biTermUniques)