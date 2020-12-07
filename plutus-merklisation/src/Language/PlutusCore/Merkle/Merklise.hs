{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Language.PlutusCore.Merkle.Merklise (analyseScripts, pruneProgram, pruneAllTypes, numberProgram)
where

import qualified Codec.Compression.GZip                          as G
import qualified Codec.Compression.GZip                          as G
import           Codec.Serialise
import           Control.Monad
import           Control.Monad.Trans.Except                      (runExceptT)
import           Crypto.Hash
import qualified Data.ByteString.Lazy                            as BSL
import           Data.Functor.Foldable
import qualified Numeric                                         (showFFloat)

import qualified Data.List
import qualified Data.Map
import qualified Data.Set

import qualified Language.PlutusCore                             as PLC
import qualified Language.PlutusCore.Merkle.CBOR                 as M
import qualified Language.PlutusCore.Merkle.Constant.Typed       as M
import           Language.PlutusCore.Merkle.Convert
import qualified Language.PlutusCore.Merkle.Evaluation.CekMarker as CekMarker
import qualified Language.PlutusCore.Merkle.Evaluation.Result    as M
import           Language.PlutusCore.Merkle.Merklisable
import qualified Language.PlutusCore.Merkle.PLCSize              as PLCSize
import qualified Language.PlutusCore.Merkle.Size                 as U
import           Language.PlutusCore.Merkle.Type
import           Language.PlutusCore.Pretty
import qualified Language.PlutusCore.Untyped.CBOR                as U ()
import qualified Language.PlutusCore.Untyped.Convert             as C
import qualified Language.PlutusCore.Untyped.DeBruijn            as D
import qualified Language.PlutusCore.Untyped.Term                as U
import qualified Language.PlutusTx.Builtins                      as B

import           Debug.Trace


{- Numbering nodes.  We replace the annotations in an AST with unique
   Integers.  We do this by passing in a tree containing all the
   natural numbers, using the number at the root to number the current
   node and left and right subtrees to number subterms etc.  This is a
   bit profligate, but has the advantage of being purely functional. }
-}

type NodeIDs = Data.Set.Set Integer

type Prog = PLC.Program PLC.TyName PLC.Name ()

data X = X
instance Serialise X where
    encode = mempty
    decode = pure X

instance Merklisable X where
    merkleHash _ = merkleHash "X"

componentStatistics ::  Prog -> Prog -> Prog -> Prog -> String

nodynamics :: M.DynamicBuiltinNameMeanings
nodynamics = M.DynamicBuiltinNameMeanings Data.Map.empty


data Numbers = Numbers {first::Integer, left::Numbers, right:: Numbers}

makeNumbers :: Integer -> Numbers
makeNumbers n = Numbers n (makeNumbers $ 2*n) (makeNumbers $ 2*n+1)

nats :: Numbers
nats = makeNumbers 1
-- An infinite tree containing each integer >= 1 exactly once
-- nats is a bad name.

numberName :: Numbers -> PLC.Name a -> PLC.Name Integer
numberName numbers (PLC.Name x s u) = PLC.Name (first numbers) s u

numberType :: Numbers -> PLC.Type PLC.TyName a -> PLC.Type PLC.TyName Integer
numberType (Numbers q l r) =
    \case
      PLC.TyVar     _ tn      -> PLC.TyVar     q (numberTyname l tn)
      PLC.TyFun     _ ty ty'  -> PLC.TyFun     q (numberType l ty) (numberType r ty')
      PLC.TyIFix    _ ty ty'  -> PLC.TyIFix    q (numberType l ty) (numberType r ty')
      PLC.TyForall  _ tn k ty -> PLC.TyForall  q (numberTyname (left l) tn) (numberKind (right l) k) (numberType r ty)
      PLC.TyBuiltin _ tb      -> PLC.TyBuiltin q tb
      PLC.TyLam     _ tn k ty -> PLC.TyLam     q (numberTyname (left l) tn) (numberKind (right l) k) (numberType r ty)
      PLC.TyApp     _ ty ty'  -> PLC.TyApp     q (numberType l ty) (numberType r ty')

substConst :: Functor f => t -> f a -> f t
substConst = fmap . const

numberBuiltin :: Numbers -> PLC.Builtin a -> PLC.Builtin Integer
numberBuiltin (Numbers q _ _)  = substConst q
-- Maybe I'm trying to be too clever here.  Success depends on the
-- fact that builtins have no subterms, which is invisible in this
-- code.  If we did have subterms, they'd all get the same q.

numberConstant :: Numbers -> PLC.Constant a -> PLC.Constant Integer
numberConstant (Numbers q _ _) = substConst q

numberTyname :: Numbers -> PLC.TyName a -> PLC.TyName Integer
numberTyname numbers (PLC.TyName n) = PLC.TyName (numberName numbers n)

numberKind :: Numbers -> PLC.Kind a -> PLC.Kind Integer
numberKind (Numbers q l r) =
    \case
     PLC.Type _            -> PLC.Type q
     PLC.KindArrow _ k1 k2 -> PLC.KindArrow q (numberKind l k1) (numberKind r k2)

numberTerm :: Numbers -> PLC.Term PLC.TyName PLC.Name a -> PLC.Term PLC.TyName PLC.Name Integer
numberTerm (Numbers q l r) =
    \case
      PLC.Var      _ n        -> PLC.Var      q (numberName l n)
      PLC.LamAbs   _ n ty t   -> PLC.LamAbs   q (numberName l n) (numberType (left l) ty) (numberTerm r t)
      PLC.TyInst   _ t ty     -> PLC.TyInst   q (numberTerm l t) (numberType r ty)
      PLC.IWrap    _ ty1 ty t -> PLC.IWrap    q (numberType (left l) ty1) (numberType (right l) ty) (numberTerm l t)
      PLC.TyAbs    _ tn k t   -> PLC.TyAbs    q (numberTyname (left l) tn) (numberKind (right l) k) (numberTerm r t)
      PLC.Apply    _ t1 t2    -> PLC.Apply    q (numberTerm l t1) (numberTerm r t2)
      PLC.Unwrap   _ t        -> PLC.Unwrap   q (numberTerm l t)
      PLC.Error    _ ty       -> PLC.Error    q (numberType l ty)
      PLC.Constant _ c        -> PLC.Constant q (numberConstant l c)
      PLC.Builtin  _ b        -> PLC.Builtin  q (numberBuiltin l b)

numberVersion :: Numbers -> PLC.Version a -> PLC.Version Integer
numberVersion (Numbers q _ _) = substConst q

numberProgram :: PLC.Program PLC.TyName PLC.Name a -> PLC.Program PLC.TyName PLC.Name Integer
numberProgram = numProg nats
    where numProg (Numbers q l r) (PLC.Program _ v t) = PLC.Program q (numberVersion l v) (numberTerm r t)


{- Pruning unused nodes.  While we're at it, let's convert numeric annotations back to units. -}

type NumSet = Data.Set.Set Integer

typeId :: PLC.Type PLC.TyName Integer -> Integer
typeId = PLC.tyLoc


-- A generic type of type-pruning funtions.
-- In our case, all types will be unused, so pruners will always be applied.
type TypePruner = NumSet -> PLC.Type PLC.TyName Integer -> Type PLC.TyName ()


pruneAllTypes :: TypePruner
pruneAllTypes used ty0 =
    if not $ Data.Set.member (typeId ty0) used
    then TyPruned () (merkleHash (fromCoreType $ () <$ ty0))
    else case ty0 of
      PLC.TyVar     _ tn      -> TyVar     () (() <$ tn)
      PLC.TyFun     _ ty ty'  -> TyFun     () (pruneAllTypes used ty) (pruneAllTypes used ty')
      PLC.TyIFix    _ ty ty'  -> TyIFix    () (pruneAllTypes used ty) (pruneAllTypes used ty')
      PLC.TyForall  _ tn k ty -> TyForall  () (() <$ tn) (() <$ fromCoreKind k) (pruneAllTypes used ty)
      PLC.TyBuiltin _ tb      -> TyBuiltin () tb
      PLC.TyLam     _ tn k ty -> TyLam     () (() <$ tn) (() <$ fromCoreKind k) (pruneAllTypes used ty)
      PLC.TyApp     _ ty ty'  -> TyApp     () (pruneAllTypes used ty) (pruneAllTypes used ty')

pruneBigTypes :: TypePruner
pruneBigTypes used ty0 =
    if not $ Data.Set.member (typeId ty0) used
    then
        let ty1 = fromCoreType $ ty0
        in if (BSL.length . serialise $ X <$ ty1) <= 34
           then () <$ ty1
           else TyPruned () (merkleHash (fromCoreType $ () <$ ty0))
    else case ty0 of
      PLC.TyVar     _ tn      -> TyVar     () (() <$ tn)
      PLC.TyFun     _ ty ty'  -> TyFun     () (pruneBigTypes used ty) (pruneBigTypes used ty')
      PLC.TyIFix    _ ty ty'  -> TyIFix    () (pruneBigTypes used ty) (pruneBigTypes used ty')
      PLC.TyForall  _ tn k ty -> TyForall  () (() <$ tn) (() <$ fromCoreKind k) (pruneBigTypes used ty)
      PLC.TyBuiltin _ tb      -> TyBuiltin () tb
      PLC.TyLam     _ tn k ty -> TyLam     () (() <$ tn) (() <$ fromCoreKind k) (pruneBigTypes used ty)
      PLC.TyApp     _ ty ty'  -> TyApp     () (pruneBigTypes used ty) (pruneBigTypes used ty')

dontPrune :: TypePruner
dontPrune _used ty = fromCoreType $ () <$ ty

termId :: PLC.Term PLC.TyName PLC.Name Integer -> Integer
termId = PLC.termLoc  -- We should rename termLoc since this isn't a location

pruneTerm :: NumSet -> TypePruner -> PLC.Term PLC.TyName PLC.Name Integer -> Term PLC.TyName PLC.Name ()
pruneTerm used pruneType t0 =
    let pruneTerm' = pruneTerm used pruneType
        pruneType' = pruneType used
    in if not $ Data.Set.member (termId t0) used
    then
        let t1 = fromCoreTerm $ () <$ t0
            threshold = 36
            -- ^ Don't Merklise anything smaller than this; note that a pruned node serialises to 36 bytes
            s = serialise $ X<$ (Prune () (merkleHash t1) :: Term PLC.TyName PLC.Name ())

            l = -- Debug.Trace.trace ("================================================================") $
                -- Debug.Trace.trace (show $ prettyPlcClassicDebug t0) $
                BSL.length (serialise $ X <$ t1)
        in if  l > threshold
           then -- Debug.Trace.trace ("Pruned term of size " ++ show l ++ ": " ++ show (PLCSize.termNumTermNodes t0) ++ " term nodes") $
                Prune () (merkleHash t1)
           else t1
    else case t0 of
           PLC.Var      _ n         -> Var      () (() <$ n)
           PLC.LamAbs   _ n ty t    -> LamAbs   () (() <$ n) (pruneType' ty) (pruneTerm' t)
           PLC.TyInst   _ t ty      -> TyInst   () (pruneTerm' t) (pruneType' ty)
           PLC.IWrap    _ ty1 ty2 t -> IWrap    () (pruneType' ty1) (pruneType' ty2) (pruneTerm' t)
           PLC.TyAbs    _ tn k t    -> TyAbs    () (() <$ tn) (() <$ fromCoreKind k) (pruneTerm' t)
           PLC.Apply    _ t1 t2     -> Apply    () (pruneTerm' t1) (pruneTerm' t2)
           PLC.Unwrap   _ t         -> Unwrap   () (pruneTerm' t)
           PLC.Error    _ ty        -> Error    () (pruneType' ty)
           PLC.Constant _ c         -> Constant () (() <$ fromCoreConstant c)
           PLC.Builtin  _ b         -> Builtin  () (() <$ fromCoreBuiltin b)

pruneProgram :: Data.Set.Set Integer -> TypePruner -> PLC.Program PLC.TyName PLC.Name Integer -> Program PLC.TyName PLC.Name ()
pruneProgram used pruneType (PLC.Program _ v t) = Program () (() <$ v) (pruneTerm used pruneType t)


-- Merklisation with thresholds

pruneTypeWithThreshold :: Int -> PLC.Type PLC.TyName b -> Type PLC.TyName ()
pruneTypeWithThreshold threshold ty0 =
    let pruneType' = pruneTypeWithThreshold threshold
        ty1 = X <$ ty0
        l = fromIntegral $ BSL.length (serialise  $ X <$ ty1)
    in if l > threshold
       then TyPruned () (merkleHash (fromCoreType $ () <$ ty0))
    else case ty0 of
      PLC.TyVar     _ tn      -> TyVar     () (() <$ tn)
      PLC.TyFun     _ ty ty'  -> TyFun     () (pruneType' ty) (pruneType' ty')
      PLC.TyIFix    _ ty ty'  -> TyIFix    () (pruneType' ty) (pruneType' ty')
      PLC.TyForall  _ tn k ty -> TyForall  () (() <$ tn) (() <$ fromCoreKind k) (pruneType' ty)
      PLC.TyBuiltin _ tb      -> TyBuiltin () tb
      PLC.TyLam     _ tn k ty -> TyLam     () (() <$ tn) (() <$ fromCoreKind k) (pruneType' ty)
      PLC.TyApp     _ ty ty'  -> TyApp     () (pruneType' ty) (pruneType' ty')

pruneTypesWithThreshold :: Int -> PLC.Term PLC.TyName PLC.Name Integer -> Term PLC.TyName PLC.Name ()
pruneTypesWithThreshold threshold t0 =
    let pruneTerm' = pruneTypesWithThreshold threshold
        pruneType' = pruneTypeWithThreshold  threshold
    in case t0 of
           PLC.Var      _ n         -> Var      () (() <$ n)
           PLC.LamAbs   _ n ty t    -> LamAbs   () (() <$ n) (pruneType' ty) (pruneTerm' t)
           PLC.TyInst   _ t ty      -> TyInst   () (pruneTerm' t) (pruneType' ty)
           PLC.IWrap    _ ty1 ty2 t -> IWrap    () (pruneType' ty1) (pruneType' ty2) (pruneTerm' t)
           PLC.TyAbs    _ tn k t    -> TyAbs    () (() <$ tn) (() <$ fromCoreKind k) (pruneTerm' t)
           PLC.Apply    _ t1 t2     -> Apply    () (pruneTerm' t1) (pruneTerm' t2)
           PLC.Unwrap   _ t         -> Unwrap   () (pruneTerm' t)
           PLC.Error    _ ty        -> Error    () (pruneType' ty)
           PLC.Constant _ c         -> Constant () (() <$ fromCoreConstant c)
           PLC.Builtin  _ b         -> Builtin  () (() <$ fromCoreBuiltin b)

pruneProgramTypesWithThreshold :: Int -> PLC.Program PLC.TyName PLC.Name Integer -> Program PLC.TyName PLC.Name ()
pruneProgramTypesWithThreshold threshold (PLC.Program _ v t) = Program () (() <$ v) (pruneTypesWithThreshold threshold t)

-- Try Merklising with a range of thresholds to see what gives us the best results

incrementalTypeMerklisationStatistics ::Prog -> Prog -> Prog -> Prog -> String
incrementalTypeMerklisationStatistics validator dataVal redeemer valData =
    let appliedValidator = apply (apply (apply validator dataVal) redeemer) valData
        numberedValidator = numberProgram validator
        program = numberedValidator `apply2` (num dataVal) `apply2` (num redeemer) `apply2` (num valData)

        thresholds = map (50*) [0..100]
        doSerialise thr = serialise . (X <$ ) $ pruneProgramTypesWithThreshold thr program
        clen = BSL.length . compress
        getInfo threshold =
            let  s = doSerialise threshold
            in show threshold ++ " " ++ show (BSL.length s) ++ " " ++ show (clen s)
        statistics = map getInfo thresholds
     in "\n"
        ++ Data.List.intercalate "\n" statistics


----- The following stuff should be somewhere else

pruneUntypedTermWithThreshold :: Int -> NumSet -> U.Term C.IntName Integer ->  U.Term C.IntName ()
pruneUntypedTermWithThreshold threshold used = prune
    where prune (t0 :: U.Term C.IntName Integer) =
              if not $ Data.Set.member (U.termLoc t0) used
              then
                  let t1 = () <$ t0
                      l = fromIntegral $ BSL.length (serialise $ X <$ t1)
                  in if  l > threshold
                     then U.Prune () (merkleHash t1)
                     else t1
              else case t0 of
                     U.Var      _ n     -> U.Var      () (() <$ n)
                     U.LamAbs   _ n t   -> U.LamAbs   () (() <$ n) (prune t)
                     U.Apply    _ t1 t2 -> U.Apply    () (prune t1) (prune t2)
                     U.Error    _       -> U.Error    ()
                     U.Constant _ c     -> U.Constant () (() <$ c)
                     U.Builtin  _ b     -> U.Builtin  () (() <$ b)
                     U.Prune    _ p     -> U.Prune    () p

pruneUntypedProgramWithThreshold :: Int -> Data.Set.Set Integer -> U.Program C.IntName Integer -> U.Program C.IntName ()
pruneUntypedProgramWithThreshold threshold used (U.Program _ v t) =
    U.Program () (() <$ v) (pruneUntypedTermWithThreshold threshold used t)


{- Once we've got the used nodes, traverse the AST;  when we find a used node,
   save its serialised size together with its number.  When we've got all these
   pairs, sort them by the serialised size, then incrementally prune more and more
   nodes, measuring the uncompressed and compressed sizes. -}

incrementalMerklisationStatistics ::Prog -> Prog -> Prog -> Prog -> String
incrementalMerklisationStatistics validator dataVal redeemer valData =
    let appliedValidator = apply (apply (apply validator dataVal) redeemer) valData
        numberedValidator = numberProgram validator
        program = numberedValidator `apply2` (num dataVal) `apply2` (num redeemer) `apply2` (num valData)
        usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins program

        numTermNodes = PLCSize.programNumTermNodes validator
        numUsedNodes = Data.Set.size usedNodes
        strippedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ numberedValidator
        thresholds = -- [0..400] --
                     -- map (50*) [0..100]
                     [0..1600]
        doSerialise thr = serialise . (X <$) $ pruneUntypedProgramWithThreshold thr usedNodes strippedValidator
        clen = BSL.length . compress
        getInfo threshold =
            let  s = doSerialise threshold
            in show threshold ++ " " ++ show (BSL.length s) ++ " " ++ show (clen s)
        statistics = map getInfo thresholds
     in "\n"
        ++ Data.List.intercalate "\n" statistics

discardUnusedNodesTerm :: NumSet -> U.Term C.IntName Integer ->  U.Term C.IntName ()
discardUnusedNodesTerm used = discardPrunes
    where discardPrunes (t0 :: U.Term C.IntName Integer) =
              if not $ Data.Set.member (U.termLoc t0) used
              then U.Error ()
              else case t0 of
                     U.Var      _ n     -> U.Var      () (() <$ n)
                     U.LamAbs   _ n t   -> U.LamAbs   () (() <$ n) (discardPrunes t)
                     U.Apply    _ t1 t2 -> U.Apply    () (discardPrunes t1) (discardPrunes t2)
                     U.Error    _       -> U.Error    ()
                     U.Constant _ c     -> U.Constant () (() <$ c)
                     U.Builtin  _ b     -> U.Builtin  () (() <$ b)
                     U.Prune    _ p     -> U.Error ()

discardUnusedNodes :: NumSet -> U.Program C.IntName Integer ->  U.Program C.IntName ()
discardUnusedNodes usedNodes (U.Program _ version body) = U.Program () (() <$ version) (discardUnusedNodesTerm usedNodes body)

componentStatistics validator dataVal redeemer ptx =
    let sizes prog = show (PLCSize.astInfo prog) ++ "/" ++ show (BSL.length (serialise $ X <$ prog))
        messages = ["\n",
                    "validator: " ++ sizes validator,
                    "dataval  : " ++ sizes dataVal,
                    "redeemer : " ++ sizes redeemer,
                    "pendingtx: " ++ sizes ptx
                   ]
    in Data.List.intercalate "\n" messages


getUsedNodes :: (Either CekMarker.CekMachineException M.EvaluationResultDef, NodeIDs) -> NodeIDs
getUsedNodes (e, nodes) =
    case e of
     Left k                             -> error $ "getUsedNodes: Left " ++ show k
     Right M.EvaluationFailure          -> nodes  -- EvaluationFailure is when we evaluate Error, which is actually OK.
     Right (M.EvaluationSuccess _term ) -> nodes

compress :: B.ByteString -> B.ByteString
compress = G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression}

-- TODO: test that if we choose a random node and prune it, the Merkle hash of the AST doesn't change.
merklisationStatistics0 :: Prog -> String
merklisationStatistics0 program =
    let s1 = serialise $ X <$ program
        numberedProgram = numberProgram program
        PLC.Program progAnn _ numberedBody = numberedProgram
        bodyAnn = PLC.termLoc numberedBody
        usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins numberedProgram
        prunedProgram = pruneProgram usedNodes pruneAllTypes numberedProgram
        s2 = serialise $ X <$ prunedProgram
        hash1 = merkleHash $ fromCoreProgram program
        hash2 = merkleHash prunedProgram

        messages = [
         "\nBefore Merklisation",
         " AST size: " ++ (show $ PLCSize.astInfo program),
         " Serialised size = " ++ (show $ BSL.length s1) ++ " bytes",
         " Compressed size = " ++ (show $ BSL.length (compress s1)) ++ " bytes",
         "",
         "After Merklisation",
         " Number of terms used during execution = " ++ (show $ Data.Set.size usedNodes) ,
         " Remaining nodes: " ++ (show $ U.programSize prunedProgram),
         " AST size: " ++ (show $ U.astInfo prunedProgram),
         " Serialised size = " ++ (show $ BSL.length s2) ++ " bytes",
         " Compressed size = " ++ (show $ BSL.length (compress s2)) ++ " bytes",
         "",
         "Merkle hash: " ++ (show hash1),
         "Merkle hash after  pruning: " ++ (show hash2)
         ]
    in Data.List.intercalate "\n" messages


--  Want raw, raw & erased, pruned, pruned & erased.  Compressed and
--  uncompressed versions for both.  Number of nodes before and after
--  pruning in a seaparate table?

-- | Count the number of pruned nodes in a term.
prunedTerms :: Term tyname name ann -> Integer
prunedTerms = cata a where
    a VarF{}              = 0
    a (TyAbsF _ _ k t)    = t
    a (ApplyF _ t t')     = t + t'
    a (LamAbsF _ _ ty t)  = t
    a ConstantF{}         = 0
    a BuiltinF{}          = 0
    a (TyInstF _ t ty)    = t
    a (UnwrapF _ t)       = t
    a (IWrapF _ ty ty' t) = t
    a (ErrorF _ ty)       = 0
    a (PruneF _ _)        = 1

-- | Count the number of AST nodes in a program.
progPrunedTerms :: Program tyname name ann -> Integer
progPrunedTerms (Program _ _ t) = prunedTerms t


merklisationStatistics ::Prog -> String
merklisationStatistics program =
    let numberedProgram = numberProgram program
        PLC.Program progAnn _ numberedBody = numberedProgram
        bodyAnn = PLC.termLoc numberedBody
        usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins numberedProgram
        numTermNodes = PLCSize.programNumTermNodes program
        numUsedNodes = Data.Set.size usedNodes
        prunedProgram1 = pruneProgram usedNodes pruneAllTypes numberedProgram
        prunedProgram2 = pruneProgram usedNodes pruneBigTypes numberedProgram
        prunedProgram3 = pruneProgram usedNodes dontPrune numberedProgram
        strippedProgram       = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ program
        strippedPrunedProgram = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.eraseMerkleProgram $ prunedProgram1
        -- When we strip a pruned program, all types are discarded so it's irrelevant what pruning method we used
        clen = BSL.length . compress

        s1  = serialise $ X<$ program
        s2  = serialise $ X<$ strippedProgram
        s3a = serialise $ X<$ prunedProgram1
        s3b = serialise $ X<$ prunedProgram2
        s3c = serialise $ X<$ prunedProgram3
        s4  = serialise $ X<$ strippedPrunedProgram
    in "\n"
         ++ "* | " ++ show numTermNodes ++ " | " ++ show numUsedNodes ++ " | "
         ++ (show $ BSL.length s1) ++ " | " ++ (show $ BSL.length s2)
         ++ " | " ++ (show $ BSL.length s3a) ++ " | " ++ (show $ BSL.length s3b) ++ " | " ++ (show $ BSL.length s3c)
         ++ " | " ++ (show $ BSL.length s4)
         ++ " | \n"
         ++ "* | (compressed) | - | "
         ++ (show $ clen s1) ++ " | "  ++ (show $ clen s2) ++ " | "
         ++ (show $ clen s3a) ++ " | "  ++ (show $ clen s3b) ++ " | "  ++ (show $ clen s3c)
         ++ " | "  ++ (show $ clen s4) ++ " |"
         ++ "\nPruned term nodes in program: " ++ show (progPrunedTerms prunedProgram1)


-- 1. Run applied validator, use results to Merklise unapplied validator and see what happens
-- 2. Repeatedly Merklise away terms (and/or types?) in descending order of serialised size and see
--    if we ever win.

-- Merklising types is always unproductive.
-- It looks as if we can sometimes do a bit better than minimisation and compression
-- if we only Merklise really big types; the uncompressed untyped Merklised version
-- can be smaller than the non-Merklised version, but it's never close to the compressed size.
-- Maybe if w care about in-memory size that'll be useful.  From the security point of view,
-- we'd presumably have to Merklise all of the unused stuff to be sure that we weren't giving
-- anything away, but that's bad from a size point of view.


apply :: Prog -> Prog -> Prog
apply = PLC.applyProgram

apply2 :: PLC.Program tyname name Integer -> PLC.Program tyname name Integer -> PLC.Program tyname name Integer
apply2 (PLC.Program _ _ t1) (PLC.Program _ _ t2) = PLC.Program (-1) (PLC.defaultVersion (-1)) (PLC.Apply (-1) t1 t2)

num :: PLC.Program PLC.TyName PLC.Name () -> PLC.Program PLC.TyName PLC.Name Integer
num p = (-1) <$ p

stringOfProg :: PrettyBy PrettyConfigPlc a => a -> String
stringOfProg prog = show . prettyPlcClassicDef $ prog


merklisationStatistics2 ::Prog -> Prog -> Prog -> Prog -> String
merklisationStatistics2 validator dataVal redeemer valData =
    let appliedValidator = apply (apply (apply validator dataVal) redeemer) valData
        numberedValidator = numberProgram validator
        program = numberedValidator `apply2` (num dataVal) `apply2` (num redeemer) `apply2` (num valData)

        usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins program
        numTermNodes = PLCSize.programNumTermNodes validator
        numUsedNodes = Data.Set.size usedNodes
        prunedValidator1 = pruneProgram usedNodes pruneAllTypes numberedValidator
        prunedValidator2 = pruneProgram usedNodes pruneBigTypes numberedValidator
        prunedValidator3 = pruneProgram usedNodes     dontPrune numberedValidator
        strippedValidator       = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ numberedValidator
        strippedPrunedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.eraseMerkleProgram $ prunedValidator1
       -- When we strip a pruned program, all types are discarded so it's irrelevant what pruning method we used
        clen = BSL.length . compress

        s1  = serialise (X <$ validator)
        s2  = serialise (X <$ strippedValidator)
        s3a = serialise (X <$ prunedValidator1)
        s3b = serialise (X <$ prunedValidator2)
        s3c = serialise (X <$ prunedValidator3)
        s4  = serialise (X <$ strippedPrunedValidator)
   in "\n" -- ++ stringOfProg validator
         ++ "* | " ++ show numTermNodes ++ " | " ++ show numUsedNodes ++ " | "
         ++ (show $ BSL.length s1) ++ " | " ++ (show $ BSL.length s2)
         ++ " | " ++ (show $ BSL.length s3a) ++ " | " ++ (show $ BSL.length s3b) ++ " | " ++ (show $ BSL.length s3c)
         ++ " | " ++ (show $ BSL.length s4)
         ++ " | \n"
         ++ "* | (compressed) | - | "
         ++ (show $ clen s1) ++ " | "  ++ (show $ clen s2) ++ " | "
         ++ (show $ clen s3a) ++ " | "  ++ (show $ clen s3b) ++ " | "  ++ (show $ clen s3c)
         ++ " | "  ++ (show $ clen s4) ++ " |"
         ++ "\nPruned term nodes in program: " ++ show (progPrunedTerms prunedValidator1)



----------------- Type abstraction/instantiation statistics -----------------

data Counts = Counts Integer Integer Integer Integer

instance Semigroup Counts
    where (Counts a b c d) <> (Counts x y z t) = Counts (a+x) (b+y) (c+z) (d+t)

instance Monoid Counts
    where mempty = Counts 0 0 0 0


analyseTypeApplications :: PLC.Term tyname name () -> Counts
analyseTypeApplications = f
    where f = \case
              PLC.Var{}              -> mempty
              PLC.Constant{}         -> mempty
              PLC.Builtin{}          -> mempty
              PLC.Error _ _          -> mempty
              PLC.LamAbs _ _ _ t     -> f t
              PLC.Unwrap _ t         -> f t
              PLC.IWrap _ _ _ t      -> f t
              PLC.Apply _ t t'       -> f t <> f t'
              PLC.TyAbs _ _ _ t      -> f t <> Counts 1 0 0 0
              PLC.TyInst _ t _       ->
                  case t of
                    PLC.TyAbs {} -> f t <> Counts 0 1 1 0
                    PLC.Var {}   -> Counts 0 1 0 1
                    _            -> f t <> Counts 0 1 0 0

-- {(abs alpha K M) A} -> M

tyAppStatistics :: Prog -> Prog -> Prog -> Prog -> String
tyAppStatistics validator _dataVal _redeemer _valData =
  let PLC.Program _ _ body = validator
      Counts appcount instcount instappcount instvarcount = analyseTypeApplications body
  in show appcount ++ "/" ++ show instcount ++ "/" ++ show instappcount ++ "/" ++ show instvarcount

---------------------- Size statistics -----------------

sizeStatistics ::Prog -> Prog -> Prog -> Prog -> String
sizeStatistics validator _dataVal _redeemer _valData =
    let
        k = C.deBruijnPLCProgram  validator
        minimisedTypedValidator   = C.deBruijnToIntPLCProgram  k
        minimisedUntypedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ validator

        s1 = serialise (X <$ validator)
        s2 = serialise (X <$ minimisedTypedValidator)
        s3 = serialise (X <$ minimisedUntypedValidator)
        clen = BSL.length . compress
   in "\n" -- ++ stringOfProg validator
         ++ "| | Uncompressed | "
         ++ (show $ BSL.length s1) ++ " | "
         ++ (show $ BSL.length s2) ++ " | "
         ++ (show $ BSL.length s3) ++ " | "
         ++ "\n"
         ++ "| | Compressed | "
         ++ (show $ clen s1) ++ " | "
         ++ (show $ clen s2) ++ " | "
         ++ (show $ clen s3) ++ " | "
         ++ "\n"

totalMerklisationOverhead ::Prog -> Prog -> Prog -> Prog -> String
totalMerklisationOverhead validator dataVal redeemer valData =
    let appliedValidator = apply (apply (apply validator dataVal) redeemer) valData
        numberedValidator = numberProgram validator
        program = numberedValidator `apply2` (num dataVal) `apply2` (num redeemer) `apply2` (num valData)

        usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins program

        minimisedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ numberedValidator

        erasedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ numberedValidator
        merklisedValidator = pruneUntypedProgramWithThreshold  0 usedNodes erasedValidator

        clen = BSL.length . compress

        erased   = serialise (X <$ erasedValidator)
        merklised = serialise (X <$ merklisedValidator)

        overhead s1 s2 =
            let n1 = BSL.length s1
                n2 = BSL.length s2
                increase :: Double = 100.0 * (fromIntegral n1) / (fromIntegral n2)
            in Numeric.showFFloat (Just 2) increase "%"
   in "\n"
         ++ "* Uncompressed: "  ++ overhead merklised erased ++ "\n"
         ++ "* Compressed:   "  ++ overhead (compress merklised) (compress erased)


-- Analyse Merklised validators using near-optimal Merklisation thresholds
-- as indicated by incrementalMerklisationStatistics.
finalMerklisationStatistics :: Prog -> Prog -> Prog -> Prog -> String
finalMerklisationStatistics validator dataVal redeemer valData =
    let appliedValidator = apply (apply (apply validator dataVal) redeemer) valData
        numberedValidator = numberProgram validator
        program = numberedValidator `apply2` (num dataVal) `apply2` (num redeemer) `apply2` (num valData)

        usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins program
        numTermNodes = PLCSize.programNumTermNodes validator
        numUsedNodes = Data.Set.size usedNodes

        minimisedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ numberedValidator

        erasedValidator = C.deBruijnToIntProgram . C.deBruijnUntypedProgram . C.erasePLCProgram $ numberedValidator
        prunedValidator1 = pruneUntypedProgramWithThreshold  34 usedNodes erasedValidator
        prunedValidator2 = pruneUntypedProgramWithThreshold 150 usedNodes erasedValidator
        unhashedValidator = discardUnusedNodes usedNodes erasedValidator

        clen = BSL.length . compress

        unerased = serialise (X <$ validator)
        erased   = serialise (X <$ erasedValidator)   -- Unmerklised validator
        spv1     = serialise (X <$ prunedValidator1)  -- Merklised, optimal threshold for uncompressed code
        spv2     = serialise (X <$ prunedValidator2)  -- Merklised, optimal threshold for compressed code
        unhashed = serialise (X <$ unhashedValidator) -- Unused nodes replaced with Error
   in "\n" -- ++ stringOfProg validator
         ++ "* | "  ++ (show $ BSL.length unerased)
         ++ " | " ++ show numTermNodes
         ++ " | " ++ show numUsedNodes
         ++ " | " ++ (show $ BSL.length erased)
         ++ " | " ++ (show $ BSL.length spv1)
         ++ " | " ++ (show $ BSL.length unhashed)
         ++ " | " ++ (show $ clen erased)
         ++ " | " ++ (show $ clen spv2)
         ++ " | " ++ (show $ clen unhashed)
         ++ " | \n"


-- The lets us expose one of the analsyes above for use elsewhere:
-- specifically, this is used in Ledger.Scripts (in plutus-wallet-api)
-- to enable us to insert some analysis code in the use case tests
-- at the point where all of the on-chain components are available.

analyseScripts ::  Prog -> Prog -> Prog -> Prog -> String
analyseScripts = finalMerklisationStatistics
