-- Various conversions on ASts and related things.
-- See also Language.PlutusCore.Merkle.Convert

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}

module Language.PlutusCore.Untyped.Convert (
                                  erasePLCTerm
                                , erasePLCProgram
                                , eraseMerkleTerm
                                , eraseMerkleProgram
                                , changeNamesUntyped
                                , anonProgram
                                , removeNameStrings
                                , removeNameStringsBi
                                , IntName (..)
                                , StringlessName (..)
                                , StringlessTyName (..)
                                , nameToIntProgram
                                , nameToIntPLCProgram
                                , deBruijnToIntProgram
                                , deBruijnToIntPLCProgram
                                , deBruijnPLCProgram
                                , deBruijnUntypedProgram
                                ) where

import           Codec.Serialise
import           Codec.Serialise.Decoding             (decodeInt)
import           Control.Monad.Trans.Except           (runExceptT)

import           PlutusPrelude

import qualified Language.PlutusCore.Core             as PLC
import qualified Language.PlutusCore.DeBruijn         as D
import qualified Language.PlutusCore.Merkle.Type      as Merkle
import qualified Language.PlutusCore.Name             as N
import qualified Language.PlutusCore.Untyped.DeBruijn as U
import           Language.PlutusCore.Untyped.Term     as U

translatePLCBuiltin :: PLC.Builtin a -> Builtin a
translatePLCBuiltin = \case
  PLC.BuiltinName x n    -> BuiltinName x n
  PLC.DynBuiltinName x n -> DynBuiltinName x n

translateMerkleBuiltin :: Merkle.Builtin a -> Builtin a
translateMerkleBuiltin = \case
  Merkle.BuiltinName x n    -> BuiltinName x n
  Merkle.DynBuiltinName x n -> DynBuiltinName x n


translatePLCConstant :: PLC.Constant a -> Constant a
translatePLCConstant = \case
     PLC.BuiltinInt x n -> BuiltinInt x n
     PLC.BuiltinBS x s  -> BuiltinBS x s
     PLC.BuiltinStr x s -> BuiltinStr x s

translateMerkleConstant :: Merkle.Constant a -> Constant a
translateMerkleConstant = \case
     Merkle.BuiltinInt x n -> BuiltinInt x n
     Merkle.BuiltinBS x s  -> BuiltinBS x s
     Merkle.BuiltinStr x s -> BuiltinStr x s


-- Erase types from a PLC program/term

erasePLCTerm :: PLC.Term _tyname name a -> Term name a
erasePLCTerm = \case
        PLC.Var x n        -> Var x n
        PLC.TyAbs _ _ _ t  -> erasePLCTerm t
        PLC.LamAbs x n _ t -> LamAbs x n (erasePLCTerm t)
        PLC.Apply x t1 t2  -> Apply  x (erasePLCTerm t1) (erasePLCTerm t2)
        PLC.Constant x c   -> Constant x (translatePLCConstant c)
        PLC.Builtin x b    -> Builtin  x (translatePLCBuiltin b)
        PLC.TyInst _ t _   -> erasePLCTerm t
        PLC.Unwrap _ t     -> erasePLCTerm t
        PLC.IWrap _ _ _ t  -> erasePLCTerm t
        PLC.Error x _      -> Error x


erasePLCProgram :: PLC.Program _ty name a -> Program name a
erasePLCProgram (PLC.Program ann version body) = Program ann version (erasePLCTerm body)

-- Erase types from a Merklised program/term

eraseMerkleTerm :: Merkle.Term _tyname name a -> Term name a
eraseMerkleTerm = \case
        Merkle.Var x n        -> Var x n
        Merkle.TyAbs _ _ _ t  -> eraseMerkleTerm t
        Merkle.LamAbs x n _ t -> LamAbs x n (eraseMerkleTerm t)
        Merkle.Apply x t1 t2  -> Apply  x (eraseMerkleTerm t1) (eraseMerkleTerm t2)
        Merkle.Constant x c   -> Constant x (translateMerkleConstant c)
        Merkle.Builtin x b    -> Builtin  x (translateMerkleBuiltin b)
        Merkle.TyInst _ t _   -> eraseMerkleTerm t
        Merkle.Unwrap _ t     -> eraseMerkleTerm t
        Merkle.IWrap _ _ _ t  -> eraseMerkleTerm t
        Merkle.Error x _      -> Error x
        Merkle.Prune x h      -> Prune x h
        -- ^ *** FIXME: this of course completely breaks Merkle
        -- hashes, but it won't affect the sizess of programs.  To do
        -- this properly we'd have to re-Merklise, possibly by having
        -- an untyped version of CekMarker.  Also, there's no relation
        -- between the merkle hashes of typed and untyped versions of
        -- the same program.


eraseMerkleProgram :: Merkle.Program _ty name a -> Program name a
eraseMerkleProgram (Merkle.Program ann version body) = Program ann version (eraseMerkleTerm body)


-- Some functions for altering names in typed programs

changeNamesTy :: (tn1 ann -> tn2 ann) -> PLC.Type tn1 ann -> PLC.Type tn2 ann
changeNamesTy g = \case
      PLC.TyVar x tn         -> PLC.TyVar x (g tn)
      PLC.TyFun x ty ty'     -> PLC.TyFun x (changeNamesTy g ty) (changeNamesTy g ty')
      PLC.TyIFix x ty ty'    -> PLC.TyIFix x (changeNamesTy g ty) (changeNamesTy g ty')
      PLC.TyForall x tn k ty -> PLC.TyForall x (g tn) k (changeNamesTy g ty)
      PLC.TyBuiltin x tb     -> PLC.TyBuiltin x tb
      PLC.TyLam x tn k ty    -> PLC.TyLam x (g tn) k (changeNamesTy g ty)
      PLC.TyApp x ty ty'     -> PLC.TyApp x (changeNamesTy g ty) (changeNamesTy g ty')

changeNamesTerm ::  (n1 ann -> n2 ann) -> (tn1 ann -> tn2 ann) -> PLC.Term tn1 n1 ann -> PLC.Term tn2 n2 ann
changeNamesTerm f g = \case
           PLC.Var x n          -> PLC.Var x (f n)
           PLC.TyAbs x tn k e   -> PLC.TyAbs x (g tn) k (changeNamesTerm f g e)
           PLC.LamAbs x n ty e  -> PLC.LamAbs x (f n) (changeNamesTy g ty) (changeNamesTerm f g e)
           PLC.Apply x e1 e2    -> PLC.Apply x (changeNamesTerm f g e1) (changeNamesTerm f g e2)
           PLC.Constant x c     -> PLC.Constant x c
           PLC.Builtin x b      -> PLC.Builtin x b
           PLC.TyInst x e ty    -> PLC.TyInst x (changeNamesTerm f g e) (changeNamesTy g ty)
           PLC.Unwrap x e       -> PLC.Unwrap x (changeNamesTerm f g e)
           PLC.IWrap x ty ty' e -> PLC.IWrap x (changeNamesTy g ty) (changeNamesTy g ty') (changeNamesTerm f g e)
           PLC.Error x ty       -> PLC.Error x (changeNamesTy g ty)

changeNamesBiTerm ::  (n1 ann -> n2 ann) -> (tn1 ann -> tn2 ann) -> PLC.BiTerm tn1 n1 ann -> PLC.BiTerm tn2 n2 ann
changeNamesBiTerm f g = \case
           PLC.BiVar x n          -> PLC.BiVar x (f n)
           PLC.BiLamAbs x n e     -> PLC.BiLamAbs x (f n) (changeNamesBiTerm f g e)
           PLC.BiApply x e1 e2    -> PLC.BiApply x (changeNamesBiTerm f g e1) (changeNamesBiTerm f g e2)
           PLC.BiConstant x c     -> PLC.BiConstant x c
           PLC.BiBuiltin x b      -> PLC.BiBuiltin x b
           PLC.BiUnwrap x e       -> PLC.BiUnwrap x (changeNamesBiTerm f g e)
           PLC.BiIWrap x ty ty' e -> PLC.BiIWrap x (changeNamesTy g ty) (changeNamesTy g ty') (changeNamesBiTerm f g e)
           PLC.BiError x ty       -> PLC.BiError x (changeNamesTy g ty)
           PLC.TyAnn x e ty       -> PLC.TyAnn x (changeNamesBiTerm f g e) (changeNamesTy g ty)

-- Map f over names, g over type names
changeNamesProgram :: (n1 ann -> n2 ann) -> (tn1 ann -> tn2 ann) -> PLC.Program tn1 n1 ann -> PLC.Program tn2  n2 ann
changeNamesProgram f g (PLC.Program ann version body) = PLC.Program ann version (changeNamesTerm f g body)

-- Map f over names, g over type names
changeNamesBiProgram :: (n1 ann -> n2 ann) -> (tn1 ann -> tn2 ann) -> PLC.BiProgram tn1 n1 ann -> PLC.BiProgram tn2  n2 ann
changeNamesBiProgram f g (PLC.BiProgram ann version body) = PLC.BiProgram ann version (changeNamesBiTerm f g body)

-- Replace names with empty strings in typed programs
anonProgram :: PLC.Program N.TyName N.Name ann -> PLC.Program N.TyName N.Name ann
anonProgram =
    changeNamesProgram anon anonTy
        where anon (N.Name ann _ u) = N.Name ann "" u
              anonTy (N.TyName n) = N.TyName (anon n)


-- Names with no string ids
data StringlessName ann = StringlessName
    { nameAttribute :: ann
    , nameUnique    :: N.Unique -- ^ A 'Unique' assigned to the name, allowing for cheap comparisons in the compiler.
    } deriving (Eq, Ord, Show, Functor, Generic, NFData)

newtype StringlessTyName ann = StringlessTyName { unTyName :: StringlessName ann }
    deriving (Show, Generic)
    deriving newtype (Eq, Ord, Functor, NFData)

removeNameStrings :: PLC.Program N.TyName N.Name ann -> PLC.Program StringlessTyName StringlessName ann
removeNameStrings = changeNamesProgram f g
              where f (N.Name ann _ u) = StringlessName ann u
                    g (N.TyName n) = StringlessTyName (f n)

removeNameStringsBi :: PLC.BiProgram N.TyName N.Name ann -> PLC.BiProgram StringlessTyName StringlessName ann
removeNameStringsBi = changeNamesBiProgram f g
              where f (N.Name ann _ u) = StringlessName ann u
                    g (N.TyName n) = StringlessTyName (f n)

-- Changing names in untyped code

changeNamesUntypedTerm :: (name1 ann -> name2 ann) -> Term name1 ann -> Term name2 ann
changeNamesUntypedTerm f = \case
        Var x n        -> Var x (f n)
        LamAbs x n t   -> LamAbs x (f n) (changeNamesUntypedTerm f t)
        Apply x t1 t2   -> Apply x (changeNamesUntypedTerm f t1) (changeNamesUntypedTerm f t2)
        Error x        -> Error x
        Constant x c   -> Constant x c
        Builtin x b    -> Builtin x b
        Prune x h      -> Prune x h
-- NOTE: Changing names will mess up the Merkle hashes, but that
-- doesn't matter too much for the purposes of this code.

changeNamesUntyped :: (name1 ann -> name2 ann) -> Program name1 ann -> Program name2 ann
changeNamesUntyped f (Program ann version body) = Program ann version (changeNamesUntypedTerm f body)


-- Names without strings and without annotations: essentially only Uniques

newtype IntName a = IntName Int
instance Serialise (IntName a) where
    encode (IntName n) = encode n
    decode = IntName <$> decodeInt

instance Show (IntName a) where
    show (IntName n) = show n

deriving instance Functor IntName

nameToInt :: N.Name a -> IntName a
nameToInt (N.Name _ _ (N.Unique uniq)) = IntName uniq

nameToIntProgram :: Program N.Name a -> Program IntName a
nameToIntProgram = changeNamesUntyped nameToInt


tyNameToInt :: N.TyName a -> IntName a
tyNameToInt (N.TyName n) = nameToInt n

nameToIntPLCProgram :: PLC.Program N.TyName N.Name a -> PLC.Program IntName IntName a
nameToIntPLCProgram = changeNamesProgram nameToInt tyNameToInt


{- To get plc source for the use cases,  add

    --ghc-options: -fplugin-opt  Language.PlutusTx.Plugin:dump-plc

   to plutus-use-cases.cabal (under 'library')and then build
   plutus-use-cases.  This will dump the source to the terminal, along
   with all the other build output. This isn't ideal, but it's a quick
   way to get PLC. The source probably won't compile though (clashes
   with built in names; also plc can't handle extensible builtins (yet)).
-}



-- A quick converter from terms using names based on deBruijn indices
-- to ones just using Ints, to see if that makes any difference to
-- compressibility.

-- deBruijnToInt :: D.DeBruijn ann -> IntName ann
-- deBruijnToInt (D.DeBruijn _attr _string (D.Index n)) = IntName (fromIntegral n)

deBruijnPLCProgram :: PLC.Program N.TyName N.Name ann -> PLC.Program D.TyDeBruijn D.DeBruijn ann
deBruijnPLCProgram p =
   case runExceptT $ D.deBruijnProgram p of
     Left e -> error e
     Right y ->
         case y of
           Left freeVarError -> error ("Error: " ++ show freeVarError)
           Right t           -> t

-- A quick converter from terms using names based on deBruijn indices
-- to ones just using Ints, to see if that makes any difference to
-- compressibility.

deBruijnToInt :: D.DeBruijn ann -> IntName ann
deBruijnToInt (D.DeBruijn _attr _string (D.Index n)) = IntName (fromIntegral n)

deBruijnToIntProgram :: U.Program D.DeBruijn ann -> U.Program IntName ann
deBruijnToIntProgram = changeNamesUntyped deBruijnToInt


deBruijnUntypedProgram :: U.Program N.Name ann -> U.Program U.DeBruijn ann
deBruijnUntypedProgram p =
   case runExceptT $ U.deBruijnProgram p of
     Left e -> error e
     Right y ->
         case y of
           Left freeVarError -> error ("Error: " ++ show freeVarError)
           Right t           -> t


tyDeBruijnToInt :: D.TyDeBruijn ann -> IntName ann
tyDeBruijnToInt (D.TyDeBruijn n) = deBruijnToInt n

deBruijnToIntPLCProgram :: PLC.Program D.TyDeBruijn D.DeBruijn ann -> PLC.Program IntName IntName ann
deBruijnToIntPLCProgram = changeNamesProgram deBruijnToInt tyDeBruijnToInt
