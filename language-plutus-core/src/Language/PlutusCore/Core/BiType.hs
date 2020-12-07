{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE KindSignatures        #-}

module Language.PlutusCore.Core.BiType
    ( Type(..)
    , BiTerm(..)
    , BiValue
    , BiProgram(..)
    , ETerm(..)
    , EValue
    , EProgram(..)
    -- * Helper functions
    , toTerm
    , termAnn
    )
where

import           PlutusPrelude

import           Language.PlutusCore.Name

import           Control.Lens
import           Data.Text                    (Text)
import           GHC.Exts                     (Constraint)
import           Instances.TH.Lift            ()
import           Language.Haskell.TH.Syntax   (Lift)

import           Language.PlutusCore.Core.Type hiding (toTerm, termAnn, typeAnn) -- (HasUniques, Builtin, Version, Kind)

{- Note [Annotations and equality]
Equality of two things does not depend on their annotations.
So don't use @deriving Eq@ for things with annotations.
-}

data BiTerm tyname name ann
    = BiVar ann (name ann) -- ^ a named variable
    | BiLamAbs ann (name ann) (BiTerm tyname name ann)
    | BiApply ann (BiTerm tyname name ann) (BiTerm tyname name ann)
    | BiConstant ann (Constant ann) -- ^ a constant term
    | BiBuiltin ann (Builtin ann)
    | BiUnwrap ann (BiTerm tyname name ann)
    | BiIWrap ann (Type tyname ann) (Type tyname ann) (BiTerm tyname name ann)
    | BiError ann (Type tyname ann)
    | TyAnn ann (BiTerm tyname name ann) (Type tyname ann) -- ^ type-annotated term
    deriving (Show, Functor, Generic, NFData, Lift)

type BiValue = BiTerm

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data BiProgram tyname name ann = BiProgram ann (Version ann) (BiTerm tyname name ann)
    deriving (Show, Functor, Generic, NFData, Lift)

type instance HasUniques (BiTerm tyname name ann)
    = (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
type instance HasUniques (BiProgram tyname name ann) = HasUniques
    (BiTerm tyname name ann)

toTerm :: BiProgram tyname name ann -> BiTerm tyname name ann
toTerm (BiProgram _ _ term) = term

termAnn :: BiTerm tyname name ann -> ann
termAnn (BiVar ann _       ) = ann
termAnn (BiApply ann _ _   ) = ann
termAnn (BiConstant ann _  ) = ann
termAnn (BiBuiltin  ann _  ) = ann
termAnn (BiUnwrap ann _    ) = ann
termAnn (BiIWrap ann _ _ _ ) = ann
termAnn (BiError ann _     ) = ann
termAnn (BiLamAbs ann _ _  ) = ann
termAnn (TyAnn ann _ _     ) = ann

-----------------------
-- Type erased terms --
-----------------------

data ETerm name ann
    = EVar ann (name ann) -- ^ a named variable
    | ELamAbs ann (name ann) (ETerm name ann)
    | EApply ann (ETerm name ann) (ETerm name ann)
    | EConstant ann (Constant ann) -- ^ a constant term
    | EBuiltin ann (Builtin ann)
    | EUnwrap ann (ETerm name ann)
    | EIWrap ann (ETerm name ann)
    | EError ann 
    deriving (Show, Functor, Generic, NFData, Lift)

type EValue = ETerm

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data EProgram name ann = EProgram ann (Version ann) (ETerm name ann)
    deriving (Show, Functor, Generic, NFData, Lift)

type instance HasUniques (ETerm name ann)
    = (HasUnique (name ann) TermUnique)
type instance HasUniques (EProgram name ann) = HasUniques
    (ETerm name ann)
