{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeFamilies #-}

module Language.PlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    , TypeF (..)
    , KindF (..)
    , BiTermF (..)
    , ETermF (..)
    ) where

import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Core.BiType
import           PlutusPrelude

import           Data.Functor.Foldable

data KindF ann x
    = TypeF ann
    | KindArrowF ann x x
    deriving (Functor)

data TypeF tyname ann x
    = TyVarF ann (tyname ann)
    | TyFunF ann x x
    | TyIFixF ann x x
    | TyForallF ann (tyname ann) (Kind ann) x
    | TyBuiltinF ann TypeBuiltin
    | TyLamF ann (tyname ann) (Kind ann) x
    | TyAppF ann x x
    deriving (Functor, Traversable, Foldable)

data TermF tyname name ann x
    = VarF ann (name ann)
    | TyAbsF ann (tyname ann) (Kind ann) x
    | LamAbsF ann (name ann) (Type tyname ann) x
    | ApplyF ann x x
    | ConstantF ann (Constant ann)
    | BuiltinF ann (Builtin ann)
    | TyInstF ann x (Type tyname ann)
    | UnwrapF ann x
    | IWrapF ann (Type tyname ann) (Type tyname ann) x
    | ErrorF ann (Type tyname ann)
    deriving (Functor, Traversable, Foldable)

data BiTermF tyname name ann x
    = BiVarF ann (name ann)
    | BiLamAbsF ann (name ann) x
    | BiApplyF ann x x
    | BiConstantF ann (Constant ann)
    | BiBuiltinF ann (Builtin ann)
    | BiUnwrapF ann x
    | BiIWrapF ann (Type tyname ann) (Type tyname ann) x
    | BiErrorF ann (Type tyname ann)
    | TyAnnF ann x (Type tyname ann)
    deriving (Functor, Traversable, Foldable)

data ETermF name ann x
    = EVarF ann (name ann)
    | ELamAbsF ann (name ann) x
    | EApplyF ann x x
    | EConstantF ann (Constant ann)
    | EBuiltinF ann (Builtin ann)
    | EUnwrapF ann x
    | EIWrapF ann x
    | EErrorF ann
    deriving (Functor, Traversable, Foldable)

type instance Base (Kind ann) = KindF ann
type instance Base (Type tyname ann) = TypeF tyname ann
type instance Base (Term tyname name ann) = TermF tyname name ann
type instance Base (BiTerm tyname name ann) = BiTermF tyname name ann
type instance Base (ETerm name ann) = ETermF name ann

instance Recursive (Kind ann) where
    project (Type ann)           = TypeF ann
    project (KindArrow ann k k') = KindArrowF ann k k'

instance Corecursive (Kind ann) where
    embed (TypeF ann)           = Type ann
    embed (KindArrowF ann k k') = KindArrow ann k k'

instance Recursive (Type tyname ann) where
    project (TyVar ann tn)         = TyVarF ann tn
    project (TyFun ann ty ty')     = TyFunF ann ty ty'
    project (TyIFix ann pat arg)   = TyIFixF ann pat arg
    project (TyForall ann tn k ty) = TyForallF ann tn k ty
    project (TyBuiltin ann b)      = TyBuiltinF ann b
    project (TyLam ann tn k ty)    = TyLamF ann tn k ty
    project (TyApp ann ty ty')     = TyAppF ann ty ty'

instance Corecursive (Type tyname ann) where
    embed (TyVarF ann tn)         = TyVar ann tn
    embed (TyFunF ann ty ty')     = TyFun ann ty ty'
    embed (TyIFixF ann pat arg)   = TyIFix ann pat arg
    embed (TyForallF ann tn k ty) = TyForall ann tn k ty
    embed (TyBuiltinF ann b)      = TyBuiltin ann b
    embed (TyLamF ann tn k ty)    = TyLam ann tn k ty
    embed (TyAppF ann ty ty')     = TyApp ann ty ty'

instance Recursive (Term tyname name ann) where
    project (Var ann n)           = VarF ann n
    project (TyAbs ann n k t)     = TyAbsF ann n k t
    project (LamAbs ann n ty t)   = LamAbsF ann n ty t
    project (Apply ann t t')      = ApplyF ann t t'
    project (Constant ann c)      = ConstantF ann c
    project (Builtin ann bi)      = BuiltinF ann bi
    project (TyInst ann t ty)     = TyInstF ann t ty
    project (Unwrap ann t)        = UnwrapF ann t
    project (IWrap ann pat arg t) = IWrapF ann pat arg t
    project (Error ann ty)        = ErrorF ann ty

instance Corecursive (Term tyname name ann) where
    embed (VarF ann n)           = Var ann n
    embed (TyAbsF ann n k t)     = TyAbs ann n k t
    embed (LamAbsF ann n ty t)   = LamAbs ann n ty t
    embed (ApplyF ann t t')      = Apply ann t t'
    embed (ConstantF ann c)      = Constant ann c
    embed (BuiltinF ann bi)      = Builtin ann bi
    embed (TyInstF ann t ty)     = TyInst ann t ty
    embed (UnwrapF ann t)        = Unwrap ann t
    embed (IWrapF ann pat arg t) = IWrap ann pat arg t
    embed (ErrorF ann ty)        = Error ann ty

instance Recursive (BiTerm tyname name ann) where
    project (BiVar ann n)           = BiVarF ann n
    project (BiLamAbs ann n t)      = BiLamAbsF ann n t
    project (BiApply ann t t')      = BiApplyF ann t t'
    project (BiConstant ann c)      = BiConstantF ann c
    project (BiBuiltin ann bi)      = BiBuiltinF ann bi
    project (BiUnwrap ann t)        = BiUnwrapF ann t
    project (BiIWrap ann pat arg t) = BiIWrapF ann pat arg t
    project (BiError ann ty)        = BiErrorF ann ty
    project (TyAnn ann t ty)        = TyAnnF ann t ty

instance Corecursive (BiTerm tyname name ann) where
    embed (BiVarF ann n)           = BiVar ann n
    embed (BiLamAbsF ann n t)      = BiLamAbs ann n t
    embed (BiApplyF ann t t')      = BiApply ann t t'
    embed (BiConstantF ann c)      = BiConstant ann c
    embed (BiBuiltinF ann bi)      = BiBuiltin ann bi
    embed (BiUnwrapF ann t)        = BiUnwrap ann t
    embed (BiIWrapF ann pat arg t) = BiIWrap ann pat arg t
    embed (BiErrorF ann ty)        = BiError ann ty
    embed (TyAnnF ann t ty)        = TyAnn ann t ty

instance Recursive (ETerm name ann) where
    project (EVar ann n)           = EVarF ann n
    project (ELamAbs ann n t)      = ELamAbsF ann n t
    project (EApply ann t t')      = EApplyF ann t t'
    project (EConstant ann c)      = EConstantF ann c
    project (EBuiltin ann bi)      = EBuiltinF ann bi
    project (EUnwrap ann t)        = EUnwrapF ann t
    project (EIWrap ann t) = EIWrapF ann t
    project (EError ann)        = EErrorF ann

instance Corecursive (ETerm name ann) where
    embed (EVarF ann n)           = EVar ann n
    embed (ELamAbsF ann n t)      = ELamAbs ann n t
    embed (EApplyF ann t t')      = EApply ann t t'
    embed (EConstantF ann c)      = EConstant ann c
    embed (EBuiltinF ann bi)      = EBuiltin ann bi
    embed (EUnwrapF ann t)        = EUnwrap ann t
    embed (EIWrapF ann t) = EIWrap ann t
    embed (EErrorF ann)        = EError ann
