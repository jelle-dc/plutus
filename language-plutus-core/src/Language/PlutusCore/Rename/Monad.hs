-- | The monad that the renamer runs in and related infrastructure.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Language.PlutusCore.Rename.Monad
    ( RenameT (..)
    , ScopedRenameT
    , Renaming (..)
    , TypeRenaming
    , ScopedRenaming (..)
    , HasRenaming (..)
    , scopedRenamingTypes
    , scopedRenamingTerms
    , runRenameT
    , runRenameT'
    , lookupNameM
    , renameNameM
    , withFreshenedName
    , withFreshenedName'
    , withRenamedName
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.Trans.Writer.CPS
import           Data.Set
import           Debug.Trace

-- | The monad the renamer runs in.
newtype RenameT ren m a = RenameT
    { unRenameT :: ReaderT ren m a
    } deriving
        ( Functor, Applicative, Alternative, Monad
        , MonadReader ren
        , MonadQuote
        )

-- | A renaming is a mapping from old uniques to new ones.
newtype Renaming unique = Renaming
    { unRenaming :: UniqueMap unique unique
    } deriving (Semigroup, Monoid)

-- | A type-level renaming.
-- Needed for instantiating functions running over types in generic @RenameT ren m@ to
-- a particular type of renaming.
type TypeRenaming = Renaming TypeUnique

-- | A class that specifies which 'Renaming' a @ren@ has inside.
-- A @ren@ can contain several 'Renaming's (like 'Scoped', for example).
class Coercible unique Unique => HasRenaming ren unique where
    renaming :: Lens' ren (Renaming unique)

-- | Scoping-aware mapping from locally unique uniques to globally unique uniques.
data ScopedRenaming = ScopedRenaming
    { _scopedRenamingTypes :: Renaming TypeUnique
    , _scopedRenamingTerms :: Renaming TermUnique
    }

makeLenses ''ScopedRenaming

type ScopedRenameT = RenameT ScopedRenaming

instance Semigroup ScopedRenaming where
    ScopedRenaming types1 terms1 <> ScopedRenaming types2 terms2 =
        ScopedRenaming (types1 <> types2) (terms1 <> terms2)

instance Monoid ScopedRenaming where
    mempty = ScopedRenaming mempty mempty

instance (Coercible unique1 Unique, unique1 ~ unique2) =>
        HasRenaming (Renaming unique1) unique2 where
    renaming = id

instance HasRenaming ScopedRenaming TypeUnique where
    renaming = scopedRenamingTypes . renaming

instance HasRenaming ScopedRenaming TermUnique where
    renaming = scopedRenamingTerms . renaming

-- | Run a 'RenameT' computation with an empty renaming.
runRenameT :: Monoid ren => RenameT ren m a -> m a
runRenameT (RenameT a) = runReaderT a mempty

runRenameT' :: (Monoid ren, Ord unique) => WriterT (Set (unique, unique)) (RenameT ren m) a -> m (a, Set (unique, unique))
runRenameT' = runRenameT . runWriterT
    
-- | Map the underlying representation of 'Renaming'.
mapRenaming
    :: (UniqueMap unique unique -> UniqueMap unique unique)
    -> Renaming unique
    -> Renaming unique
mapRenaming = coerce

-- | Save the mapping from the @unique@ of a name to a new @unique@.
insertByNameM
    :: (HasUnique name unique, HasRenaming ren unique)
    => name -> unique -> ren -> ren
insertByNameM name = over renaming . mapRenaming . insertByName name

-- | Look up the new unique a name got mapped to.
lookupNameM
    :: (HasUnique name unique, HasRenaming ren unique, Monad m)
    => name -> RenameT ren m (Maybe unique)
lookupNameM name = asks $ lookupName name . unRenaming . view renaming

-- | Rename a name that has a unique inside.
renameNameM
    :: (HasRenaming ren unique, HasUnique name unique, Monad m)
    => name -> RenameT ren m name
renameNameM name = do
    mayUniqNew <- lookupNameM name
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

-- | Replace the unique in a name by a new unique, save the mapping
-- from the old unique to the new one and supply the updated value to a continuation.
withFreshenedName
    :: (HasRenaming ren unique, HasUnique name unique, MonadQuote m)
    => name -> (name -> RenameT ren m c) -> RenameT ren m c
withFreshenedName nameOld k = do
    uniqNew <- coerce <$> freshUnique
    local (insertByNameM nameOld uniqNew) $ k (nameOld & unique .~ uniqNew)

withFreshenedName'
    :: (HasRenaming ren unique, HasUnique name unique, MonadQuote m, Ord unique)
    => name -> (name -> RenameT ren m c) -> WriterT (Set (unique, unique)) (RenameT ren m) c
withFreshenedName' nameOld k = do
    uniqNew <- lift $ coerce <$> freshUnique
    tell $ singleton (nameOld ^. unique, uniqNew)
    when ((unUnique $ coerce $ uniqNew) == 7168) $ traceM "created' 7168"
    traceM $ "OLD: " ++ (show $ unUnique $ coerce $ nameOld ^. unique)
    traceM $ "NEW: " ++ (show $ unUnique $ coerce $ uniqNew)
    lift $ local (insertByNameM nameOld uniqNew) $ k (nameOld & unique .~ uniqNew)

-- | Run a 'RenameT' computation in the environment extended by the mapping from an old name
-- to a new one.
withRenamedName
    :: (HasRenaming ren unique, HasUnique name unique, Monad m)
    => name -> name -> RenameT ren m c -> RenameT ren m c
withRenamedName old new = local $ insertByNameM old (new ^. unique)