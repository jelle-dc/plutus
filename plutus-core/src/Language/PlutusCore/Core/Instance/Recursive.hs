{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module Language.PlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    , TypeF (..)
    , KindF (..)
    ) where

import           Language.PlutusCore.Core.Type
import           PlutusPrelude

import           Data.Functor.Foldable.TH
import Control.Lens
import Language.PlutusCore.Name
import Data.Functor.Foldable
import Data.Traversable.TreeLike

$(join <$> traverse makeBaseFunctor [''Kind, ''Type, ''Term])

-- instance TreeLike (Term TyName Name uni fun) where
--   treeTraverse = _

instance Plated (Term TyName Name uni fun a) where
  plate = gplate