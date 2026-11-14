{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      : Synthesis.Builder
Description : Lowers the core AST to a dataflow graph (DFG) of 'DNode's, wiring ports and managing environments/aliases.
Copyright   :
License     :
Maintainer  : ricardofilhoschool@gmail.com
Stability   : experimental
Portability : portable

This module builds a 'DFG' from a 'Syntax.Program'. It:

* Tracks lexical environments and free variables during synthesis.
* Emits nodes/edges, including fan-out via an alias mechanism.
* Handles applications (including n-ary flattening), conditionals, lists/tuples.
* Creates call/return groups for function calls and lambdas.
* Assigns names to @Super@ blocks via 'Semantic.assignSuperNames' before building.
-}
module Synthesis.Builder
  ( DFG
  , buildProgram
  ) where

import           Prelude hiding (lookup)
import           Control.Monad          (forM, forM_, zipWithM, zipWithM_, when, foldM)
import           Control.Monad.State    (StateT, get, put, runStateT, gets, modify)
import           Control.Monad.Trans    (lift)
import           Data.Maybe             (listToMaybe, catMaybes)
import           GHC.Float              (castFloatToWord32)
import qualified Data.Map              as M
import qualified Data.Set              as S

import           Analysis.Semantic     (assignSuperNames, desugarProgram, topTypes)
import qualified Analysis.Semantic     as Sem
import           Syntax
import           Types                  (DGraph(..), Edge, NodeId, emptyGraph, addNode, addEdge)
import           Port                   (Port(..), (-->))
import           Unique                 (Unique, evalUnique, freshId)
import           Node                   (DNode(..), out1Port)

-- Grafo final

-- | Final dataflow graph specialized to 'DNode'.
type DFG = DGraph DNode

-- Ambiente

-- | Synthesized value of an expression.
--
-- * 'Scalar': a single port (scalars, and lists/tuples in the legacy
--   pair encoding built by the list supers).
-- * 'Stream': a statically sized, length-prefixed stream: the count port
--   (an int node) plus one payload port per position @0..N-1@.
-- * 'DStream': a dynamic, loop-carried stream. With t0 the tag of the
--   context that owns it: 'dsCount' is the element count at tag t0, and
--   element k arrives on 'dsElem' at tag t0+1+k together with its index k on
--   'dsIdx' (the index is what lets head/tail pick elements out).
data Val
  = Scalar Port
  | Stream Port [Port]
  | DStream { dsCount :: Port, dsElem :: Port, dsIdx :: Port }
  | VTup [Val]               -- ^ tuple; components keep their own representation

-- | Builder-time binding: either a realized 'Val' or a lambda to be built.
data Binding = BVal Val | BLam [Ident] Expr

-- | A single-scope environment mapping identifiers to 'Binding'.
type Env = M.Map Ident Binding

-- | Aliases for a producer output identified by ('NodeId', output name).
type AliasMap    = M.Map (NodeId, String) [Port]

-- | Stack of currently active (being-built) functions.
type ActiveStack = [Ident]

-- | Global state for the builder pass.
data BuildS = BuildS
  { bsGraph      :: !DFG           -- ^ Accumulated graph.
  , bsEnv        :: ![Env]         -- ^ Environment stack (innermost at head).
  , bsAliases    :: !AliasMap      -- ^ Extra outputs that mirror a producer port.
  , bsActive     :: !ActiveStack   -- ^ Functions under construction (re-entrancy guard).
  , bsFloatFuns  :: !(S.Set Ident) -- ^ Functions observed in float contexts.
  , bsListFuns   :: !(S.Set Ident) -- ^ Functions that build/return lists.
  , bsRetVals    :: !(M.Map Ident Port) -- ^ Return value port for each function.
  , bsGuard      :: !(Maybe Port)  -- ^ Optional guard for gating calls in branches.
  , bsTopDecls   :: !(M.Map Ident ([Ident], Expr)) -- ^ Top-level functions with parameters.
  , bsRecFuns    :: !(S.Set Ident) -- ^ Top-level functions on a call cycle.
  , bsLocalFuns  :: !(S.Set Ident) -- ^ Names bound by local (let) declarations.
  , bsInLoop     :: !Bool          -- ^ Building inside a loop body (no nested loops).
  , bsScopeK     :: !Int               -- ^ Scope-level call counter for unique k values (reset on withActive).
  , bsTypes      :: !(M.Map Ident Sem.Type) -- ^ Inferred types of the top-level declarations.
  , bsMoveRets   :: ![(NodeId, Maybe Ident)] -- ^ Element-move rets and the function whose exec they run in.
  }

-- | Initial empty builder state.
emptyS :: BuildS
emptyS = BuildS emptyGraph [M.empty] M.empty [] S.empty S.empty M.empty Nothing M.empty S.empty S.empty False 0 M.empty []

-- | Builder monad with unique-id generation.
newtype Build a = Build { unBuild :: StateT BuildS Unique a }
  deriving (Functor, Applicative, Monad)

-- | Execute a 'Build' computation, returning the result and final state.
runBuild :: Build a -> (a, BuildS)
runBuild m = evalUnique (runStateT (unBuild m) emptyS)

-- escopo ----------------------------------------------------------------

-- | Push a fresh environment onto the stack.
pushEnv, popEnv :: Build ()
pushEnv = Build $ modify (\s -> s { bsEnv = M.empty : bsEnv s })

-- | Pop the current environment (no-op on empty).
popEnv  = Build $ modify (\s -> case bsEnv s of [] -> s; (_:rs) -> s { bsEnv = rs })

-- | Run a computation with a temporary fresh environment.
withEnv :: Build a -> Build a
withEnv m = do pushEnv; x <- m; popEnv; pure x

-- | Run a computation with a temporary guard (used to gate calls in branches).
withGuard :: Port -> Build a -> Build a
withGuard guard m = do
  oldGuard <- Build $ gets bsGuard
  combined <- case oldGuard of
    Nothing -> pure guard
    Just g0 -> do
      g1 <- alignExecTo guard g0
      andP guard g1
  Build $ modify (\s' -> s' { bsGuard = Just combined })
  r <- m
  Build $ modify (\s' -> s' { bsGuard = oldGuard })
  pure r

-- | Run a computation with guard cleared (used when building function bodies).
withNoGuard :: Build a -> Build a
withNoGuard m = do
  s <- Build get
  Build $ put s { bsGuard = Nothing }
  r <- m
  Build $ modify (\s' -> s' { bsGuard = bsGuard s })
  pure r

-- | Apply the current guard to a value if one is active.
guardIfNeeded :: Port -> Build Port
guardIfNeeded p = do
  mg <- Build $ gets bsGuard
  case mg of
    Nothing -> pure p
    Just g  -> do
      gTok <- guardToken g
      mc <- getConstI p
      case mc of
        Just k -> do
          p0 <- withNoGuard (constI k)
          p' <- alignExecTo gTok p0
          sid <- newNode "steer" (NSteer "")
          connect gTok (InstPort sid "0")
          connect p'   (InstPort sid "1")
          pure (SteerPort sid "t")
        Nothing -> do
          g' <- alignGuardTo p gTok
          sid <- newNode "steer" (NSteer "")
          connect g' (InstPort sid "0")
          connect p  (InstPort sid "1")
          pure (SteerPort sid "t")

-- | Produce a branch execution token from a guard.
-- The token carries the guard value in its exec/tag so it can be used
-- as the callsnd operand to trigger a single branch execution.
guardToken :: Port -> Build Port
guardToken g = do
  one <- withNoGuard (constI 1)
  one' <- alignExecTo g one
  sid <- newNode "steer" (NSteer "")
  connect g    (InstPort sid "0")
  connect one' (InstPort sid "1")
  pure (SteerPort sid "t")

-- | Align a value's exec/tag to a guard port (so steers can match).
alignExecTo :: Port -> Port -> Build Port
alignExecTo guard val = do
  mc <- getConstI val
  case mc of
    Just k -> constFrom guard k
    Nothing -> retagTo guard val

-- | Align exec tags ignoring tag matching (exec-only).
alignExecToExecOnly :: Port -> Port -> Build Port
alignExecToExecOnly guard val = do
  mc <- getConstI val
  case mc of
    Just k -> constFrom guard k
    Nothing -> retagToExecOnly guard val

-- | Retag a value to match a tag source (uses tagval/valtag).
retagTo :: Port -> Port -> Build Port
retagTo tagSrc val = do
  tv <- newNode "tagval" (NTagVal "")
  connectPlus tagSrc (InstPort tv "0")
  vt <- newNode "valtag" (NValTag "")
  connectPlus val (InstPort vt "0")
  connectPlus (out0 tv) (InstPort vt "1")
  pure (out0 vt)

-- | Retag a value to match a tag source using exec-only matching.
-- Encodes the tag as a negative marker so TALM ignores tag matching.
retagToExecOnly :: Port -> Port -> Build Port
retagToExecOnly tagSrc val = do
  tv <- newNode "tagval" (NTagVal "")
  connectPlus tagSrc (InstPort tv "0")
  one <- constFrom tagSrc 1
  tv1 <- addI (out0 tv) 1
  z <- constFrom tagSrc 0
  neg <- bin2 "sub" (NSub "") z tv1
  vt <- newNode "valtag" (NValTag "")
  connectPlus val (InstPort vt "0")
  connectPlus neg (InstPort vt "1")
  pure (out0 vt)

-- | Retag a value to a constant tag k using exec-only matching.
retagToConstTagExecOnly :: Int -> Port -> Build Port
retagToConstTagExecOnly k val = do
  negK <- constFrom val (-(k + 1))
  vt <- newNode "valtag" (NValTag "")
  connectPlus val (InstPort vt "0")
  connectPlus negK (InstPort vt "1")
  pure (out0 vt)

-- | Increment tag of a value (inctag).
incTag :: Port -> Build Port
incTag p = do
  nid <- newNode "inctag" (NIncTag "")
  connectPlus p (InstPort nid "0")
  pure (out0 nid)

-- | Align a guard's exec/tag to match a value (so steers can fire).
alignGuardTo :: Port -> Port -> Build Port
alignGuardTo val guard = do
  mc <- getConstI guard
  case mc of
    Just k -> constFrom val k
    Nothing -> retagTo val guard

-- | Record the canonical return-value port for a (zero-argument) function.
setRetVal :: Ident -> Port -> Build ()
setRetVal f p = Build $ modify (\s -> s { bsRetVals = M.insert f p (bsRetVals s) })

-- | Insert a 'Binding' for an identifier into the current environment.
insertB :: Ident -> Binding -> Build ()
insertB x b = Build $ modify $ \s -> case bsEnv s of
  (e:rs) -> s { bsEnv = M.insert x b e : rs }
  []     -> s

-- | Look up an identifier through the stacked environments (inner to outer).
lookupB :: Ident -> Build (Maybe Binding)
lookupB x = Build $ gets $ \s ->
  let go []     = Nothing
      go (e:rs) = maybe (go rs) Just (M.lookup x e)
  in go (bsEnv s)

-- | Update a binding at the scope where it was originally defined.
-- Unlike 'insertB' (which inserts into the innermost scope), this finds
-- the scope that already contains the identifier and updates it there.
-- This prevents duplicate evaluation of thunks across scope boundaries.
updateB :: Ident -> Binding -> Build ()
updateB x b = Build $ modify $ \s -> s { bsEnv = go (bsEnv s) }
  where
    go []     = []
    go (e:rs)
      | M.member x e = M.insert x b e : rs
      | otherwise     = e : go rs

-- marcação de função float ---------------------------------------------

-- | Mark a function as having been used in a floating-point context.
markFloatFun :: Ident -> Build ()
markFloatFun f = Build $ modify (\s -> s { bsFloatFuns = S.insert f (bsFloatFuns s) })

-- | Check whether a function is marked as float.
isFloatFun :: Ident -> Build Bool
isFloatFun f = Build $ gets (\s -> S.member f (bsFloatFuns s))

-- | Mark a function as building/returning lists.
markListFun :: Ident -> Build ()
markListFun f = Build $ modify (\s -> s { bsListFuns = S.insert f (bsListFuns s) })

-- | Check whether a function is marked as list-producing.
isListFun :: Ident -> Build Bool
isListFun f = Build $ gets (\s -> S.member f (bsListFuns s))

-- | True if the top of the active stack is a float-marked function.
isFloatActive :: Build Bool
isFloatActive = Build $ gets $ \s -> case bsActive s of
  (f:_) -> S.member f (bsFloatFuns s)
  _     -> False

-- | True if the top of the active stack is a list-marked function.
isListActive :: Build Bool
isListActive = Build $ gets $ \s -> case bsActive s of
  (f:_) -> S.member f (bsListFuns s)
  _     -> False

-- helper: está construindo 'f' agora?

-- | Is a given function currently being built (in the active stack)?
isActiveFun :: Ident -> Build Bool
isActiveFun f = Build $ gets (\s -> f `elem` bsActive s)

-- edges + aliases ------------------------------------------------------

-- | Emit a raw 'Edge' into the graph.
emit :: Edge -> Build ()
emit e = Build $ modify (\s -> s { bsGraph = addEdge e (bsGraph s) })

-- | Conservative check for list/tuple construction in an expression.
exprHasList :: Expr -> Bool
exprHasList = \case
  Cons _ _       -> True
  List _         -> True
  Tuple _        -> True
  Lambda _ e     -> exprHasList e
  If c t e       -> exprHasList c || exprHasList t || exprHasList e
  Case scr alts  -> exprHasList scr || any (exprHasList . snd) alts
  Let ds b       -> any declHasList ds || exprHasList b
  App f x        -> exprHasList f || exprHasList x
  BinOp _ l r    -> exprHasList l || exprHasList r
  UnOp _ e       -> exprHasList e
  _              -> False

declHasList :: Decl -> Bool
declHasList (FunDecl _ _ body) = exprHasList body

exprHasFloat :: Expr -> Bool
exprHasFloat = \case
  Lit (LFloat _) -> True
  Lambda _ e     -> exprHasFloat e
  If c t e       -> exprHasFloat c || exprHasFloat t || exprHasFloat e
  Case scr alts  -> exprHasFloat scr || any (exprHasFloat . snd) alts
  Let ds b       -> any declHasFloat ds || exprHasFloat b
  App f x        -> exprHasFloat f || exprHasFloat x
  BinOp _ l r    -> exprHasFloat l || exprHasFloat r
  UnOp _ e       -> exprHasFloat e
  _              -> False

declHasFloat :: Decl -> Bool
declHasFloat (FunDecl _ _ body) = exprHasFloat body

-- | Connect two 'Port's by emitting an edge.
connect :: Port -> Port -> Build ()
connect a b = emit (a --> b)

-- | Register additional alias outputs for the same producer port.
registerAlias :: Port -> [Port] -> Build ()
registerAlias src extras = Build $ modify $ \s ->
  let k = (pNode src, pName src)
  in s { bsAliases = M.insertWith (++) k extras (bsAliases s) }

-- | Connect a destination to a source and all of its aliases.
connectPlus :: Port -> Port -> Build ()
connectPlus src dst = Build $ do
  s <- get
  let k     = (pNode src, pName src)
      alts  = M.findWithDefault [] k (bsAliases s)
      allPs = src : alts
  put s { bsGraph = foldr (\p g -> addEdge (p --> dst) g) (bsGraph s) allPs }

-- nós ------------------------------------------------------------------

-- | Create a new node with label and payload, returning its 'NodeId'.
newNode :: String -> DNode -> Build NodeId
newNode lbl nd = Build $ do
  s   <- get
  nid <- lift freshId
  let g' = addNode nid (setName lbl nd) (bsGraph s)
  put s { bsGraph = g' }
  pure nid

-- | Create an n-ary node and connect sequential inputs to its ports.
naryNode :: String -> DNode -> [Port] -> Build NodeId
naryNode lbl nd ins = do
  nid <- newNode lbl nd
  zipWithM_ (\i p -> connectPlus p (InstPort nid (show i))) [0..] ins
  pure nid

-- | Convenience accessor for the first output port of a node.
out0 :: NodeId -> Port
out0 nid = InstPort nid "0"

-- | Convenience accessor for the second output port of a node.
out1 :: NodeId -> Port
out1 nid = InstPort nid "1"

-- | Write a display name into a 'DNode' (for debugging/graphs).
setName :: String -> DNode -> DNode
setName l n = case n of
  NConstI{}   -> n{ nName = l }
  NConstF{}   -> n{ nName = l }
  NConstD{}   -> n{ nName = l }
  NAdd{}      -> n{ nName = l }
  NSub{}      -> n{ nName = l }
  NMul{}      -> n{ nName = l }
  NDiv{}      -> n{ nName = l }
  NAddI{}     -> n{ nName = l }
  NSubI{}     -> n{ nName = l }
  NMulI{}     -> n{ nName = l }
  NFMulI{}    -> n{ nName = l }
  NDivI{}     -> n{ nName = l }
  NFAdd{}     -> n{ nName = l }
  NFSub{}     -> n{ nName = l }
  NFMul{}     -> n{ nName = l }
  NFDiv{}     -> n{ nName = l }
  NDAdd{}     -> n{ nName = l }
  NBand{}     -> n{ nName = l }
  NSteer{}    -> n{ nName = l }
  NLThan{}    -> n{ nName = l }
  NGThan{}    -> n{ nName = l }
  NEqual{}    -> n{ nName = l }
  NLThanI{}   -> n{ nName = l }
  NGThanI{}   -> n{ nName = l }
  NCallGroup{}-> n{ nName = l }
  NCallSnd{}  -> n{ nName = l }
  NRetSnd{}   -> n{ nName = l }
  NRet{}      -> n{ nName = l }
  NTagVal{}   -> n{ nName = l }
  NValTag{}   -> n{ nName = l }
  NIncTag{}   -> n{ nName = l }
  NIncTagI{}  -> n{ nName = l }
  NCpHToDev{} -> n{ nName = l }
  NCpDevToH{} -> n{ nName = l }
  NCommit{}   -> n{ nName = l }
  NStopSpec{} -> n{ nName = l }
  NArg{}      -> n{ nName = l }
  NSuper{}    -> n{ nName = l }

-- codificação pares/listas ---------------------------------------------

-- Builtin supers reserved in Semantic: s0..s3
builtinListCons :: Int
builtinListCons = 0

builtinListHead :: Int
builtinListHead = 1

builtinListTail :: Int
builtinListTail = 2

builtinListIsNil :: Int
builtinListIsNil = 3

builtinPrint :: Int
builtinPrint = 4

builtinPrintList :: Int
builtinPrintList = 5

builtinPrintStr :: Int
builtinPrintStr = 6

builtinPrintFloat :: Int
builtinPrintFloat = 7

builtinPrintFloatList :: Int
builtinPrintFloatList = 8

builtinPrintFloatMatrix :: Int
builtinPrintFloatMatrix = 9

-- | Float multiply/divide: TALM has no fmul/fdiv instruction.
builtinFMul, builtinFDiv :: Int
builtinFMul = 10
builtinFDiv = 11

superNameFromNum :: Int -> String
superNameFromNum n = "s" ++ show n

superNumFromName :: String -> Int
superNumFromName ('s':rest) =
  case reads rest of
    [(n,"")] -> n
    _        -> 0
superNumFromName _ = 0

-- | Emit an integer constant node.
constI :: Int -> Build Port
constI k = do
  mg <- Build $ gets bsGuard
  case mg of
    Nothing -> newNode ("const_" ++ show k) (NConstI "" k) >>= \nid -> pure (out0 nid)
    Just g  -> constFrom g k

-- | Try to read an integer literal from a port.
getConstI :: Port -> Build (Maybe Int)
getConstI p = Build $ gets $ \s ->
  case M.lookup (pNode p) (dgNodes (bsGraph s)) of
    Just (NConstI _ k) -> Just k
    Just (NConstF _ f) -> Just (fromIntegral (castFloatToWord32 f))
    _                  -> Nothing

-- | Build an int constant aligned to a reference port's exec/tag.
constFrom :: Port -> Int -> Build Port
constFrom ref k = do
  if pNode ref == (-1)
    then newNode ("const_" ++ show k) (NConstI "" k) >>= \nid -> pure (out0 nid)
    else do
      subN <- bin2Node "sub" (NSub "") ref ref
      let z = out0 subN
      if k == 0 then pure z else addI z k

-- immediates (sem aliases!)

-- | Add immediate @k@ to input (no alias expansion).
addI :: Port -> Int -> Build Port
addI p k
  | k == 0 = retagTo p p
  | otherwise = do
      nid <- newNode ("addi_" ++ show k) (NAddI "" k)
      connect p (InstPort nid "0")
      pure (out0 nid)

-- | Subtract immediate @k@ from input (no alias expansion).
subI :: Port -> Int -> Build Port
subI p k = do
  nid <- newNode ("subi_" ++ show k) (NSubI "" k)
  connect p (InstPort nid "0")
  pure (out0 nid)

-- | Multiply by immediate @k@ (no alias expansion).
mulI :: Port -> Int -> Build Port
mulI p k = do
  nid <- newNode ("muli_" ++ show k) (NMulI "" k)
  connect p (InstPort nid "0")
  pure (out0 nid)

-- | Float negation: flip the IEEE-754 sign bit by adding 2^31 to the raw
-- bits (wraps mod 2^32). Trebuchet has no fmul/fmuli in eval.
fnegP :: Port -> Build Port
fnegP p = do
  nid <- newNode "fneg" (NAddI "" (-2147483648))
  connect p (InstPort nid "0")
  pure (out0 nid)

-- fmuli helper (sem aliases!)

-- | Port representing the empty list.
nilP :: Build Port
nilP = constI 0

-- | Predicate: is the list port equal to 'nilP'?
isNilP :: Port -> Build Port
isNilP xs = callBuiltinSuper builtinListIsNil [xs]

callBuiltinSuper :: Int -> [Port] -> Build Port
callBuiltinSuper num ins = do
  ins' <- alignExecInputs ins
  let nm = "builtin_" ++ superNameFromNum num
  nid <- naryNode nm NSuper
           { nName     = ""
           , superNum  = num
           , superOuts = 1
           , superSpec = False
           , superImm  = Nothing
           } ins'
  pure (out0 nid)

-- | Align constant inputs to a non-constant reference (keeps exec tags consistent).
alignConstInputs :: [Port] -> Build [Port]
alignConstInputs ins = do
  cs <- mapM getConstI ins
  case [ (i,p) | (i,(p,mc)) <- zip [0..] (zip ins cs), mc == Nothing ] of
    []        -> pure ins
    ((_,r):_) -> mapM (alignOne r) (zip ins cs)
  where
    alignOne _ (p, Nothing) = pure p
    alignOne r (p, Just k)  = do _ <- pure p; constFrom r k

-- | Align all inputs (constants and non-constants) to a single reference exec/tag.
alignExecInputs :: [Port] -> Build [Port]
alignExecInputs ins = do
  cs <- mapM getConstI ins
  case [ p | (p,mc) <- zip ins cs, mc == Nothing ] of
    []    -> pure ins
    (r:_) -> mapM (alignOne r) (zip ins cs)
  where
    alignOne r (p, Just k)  = do _ <- pure p; constFrom r k
    alignOne _ (p, Nothing) = pure p

-- | Encode a pair/list cell via builtin list cons.
pairEnc :: Port -> Port -> Build Port
pairEnc a b = do
  -- Using cons implies list construction in the current function.
  act <- Build $ gets bsActive
  case act of
    (f:_) -> markListFun f
    _     -> pure ()
  ins <- alignExecInputs [a, b]
  case ins of
    [a', b'] -> do
      ma <- getConstI a'
      mb <- getConstI b'
      b'' <- if ma == Nothing && mb == Nothing
               then retagTo a' b'
               else pure b'
      callBuiltinSuper builtinListCons [a', b'']
    _        -> callBuiltinSuper builtinListCons [a, b]

-- | Decode first component from encoded pair.
fstDec :: Port -> Build Port
fstDec p = callBuiltinSuper builtinListHead [p]

-- | Decode second component from encoded pair.
sndDec :: Port -> Build Port
sndDec p = callBuiltinSuper builtinListTail [p]

-- | Local right-associative monadic fold (used for list construction).
foldrM' :: (a -> b -> Build b) -> b -> [a] -> Build b
foldrM' f z0 = go
  where
    go []     = pure z0
    go (y:ys) = do r <- go ys
                   f y r

-- streams estáticos ------------------------------------------------------

-- | Re-encode a value in the legacy pair encoding (list boundary).
streamToPair :: Val -> Build Port
streamToPair = \case
  Scalar p      -> pure p
  Stream _ []   -> nilP
  Stream _ ps   -> do z <- nilP; foldrM' pairEnc z ps
  DStream c e _ -> do
    -- Right fold with cons over the elements (pair encoding at a boundary).
    nil0 <- constFrom c 0
    backFold c [] c e nil0 (\_ h acc -> pairEnc h acc)
  VTup vs       -> do ps <- mapM asScalar vs; z <- nilP; foldrM' pairEnc z ps

-- | Use a value in scalar context; streams are re-encoded via 'streamToPair'.
asScalar :: Val -> Build Port
asScalar = streamToPair

-- | Synthesize an expression and use it in scalar context.
goScalar :: Expr -> Build Port
goScalar e = goExpr e >>= asScalar

-- | Static outcome of matching a pattern against a value of known shape.
data StaticMatch = SMNo | SMYes | SMDyn
  deriving (Eq)

-- | Shape of a value as far as static matching is concerned.
data Shape = SScalar | SStream Int | SDyn | STup [Shape]

-- | Classify a pattern against a shape without emitting nodes.
staticMatch :: Pattern -> Shape -> StaticMatch
staticMatch pat sh = case (pat, sh) of
  (PWildcard, _)          -> SMYes
  (PVar _, _)             -> SMYes
  (PTuple ps, STup shs)
    | length ps == length shs -> both (zipWith staticMatch ps shs)
  (_, STup _)             -> SMNo
  (_, SScalar)            -> SMDyn
  (PLit _, SDyn)          -> SMNo
  (PTuple _, SDyn)        -> SMNo
  (_, SDyn)               -> SMDyn
  (PList ps, SStream n)   -> seqM n ps
  (PTuple ps, SStream n)  -> seqM n ps
  (PCons ph pt, SStream n)
    | n == 0              -> SMNo
    | otherwise           -> both [staticMatch ph SScalar, staticMatch pt (SStream (n - 1))]
  (PLit _, SStream _)     -> SMNo
  where
    seqM n ps
      | length ps /= n = SMNo
      | otherwise      = both [ staticMatch q SScalar | q <- ps ]
    both ms
      | SMNo `elem` ms  = SMNo
      | SMDyn `elem` ms = SMDyn
      | otherwise       = SMYes

-- | Shape of a value.
shapeOf :: Val -> Shape
shapeOf = \case
  Scalar _    -> SScalar
  Stream _ ps -> SStream (length ps)
  DStream{}   -> SDyn
  VTup vs     -> STup (map shapeOf vs)

-- | Build the bindings (and runtime predicate, if any) for a pattern that
-- 'staticMatch' did not reject. @Nothing@ means statically true.
matchVal :: Val -> Pattern -> Build (Maybe Port, [(Ident, Val)])
matchVal v pat = case (pat, v) of
  (PWildcard, _) -> pure (Nothing, [])
  (PVar x, _)    -> pure (Nothing, [(x, v)])
  (_, Scalar p)  -> do
    (pp, bs) <- patPred p pat
    pure (Just pp, [ (x, Scalar q) | (x, q) <- bs ])
  (PList ps, Stream _ xs)  -> allOf (zipWith (\q x -> matchVal (Scalar x) q) ps xs)
  (PTuple ps, Stream _ xs) -> allOf (zipWith (\q x -> matchVal (Scalar x) q) ps xs)
  (PCons ph pt, Stream c (x:xs)) -> do
    rh <- matchVal (Scalar x) ph
    rt <- case pt of
            PWildcard -> pure (Nothing, [])
            _         -> do c' <- subI c 1
                            matchVal (Stream c' xs) pt
    allOf [pure rh, pure rt]
  (PTuple ps, VTup vs) -> allOf (zipWith (\q w -> matchVal w q) ps vs)
  (PList [], DStream c _ _) -> do
    z  <- constFrom c 0
    eq <- bin2 "equal" (NEqual "") c z
    pure (Just eq, [])
  (PList (q:qs), DStream{}) -> matchVal v (PCons q (PList qs))
  (PCons ph pt, DStream c _ _) -> do
    z  <- constFrom c 0
    ne <- bin2 "gthan" (NGThan "") c z
    h  <- dsHead v
    rh <- matchVal (Scalar h) ph
    rt <- case pt of
            PWildcard -> pure (Nothing, [])
            _         -> do t <- dsTail v; matchVal t pt
    allOf [pure (Just ne, []), pure rh, pure rt]
  _ -> do f <- falseP; pure (Just f, [])
  where
    allOf ms = do
      rs <- sequence ms
      let preds = catMaybes (map fst rs)
          bs    = concatMap snd rs
      case preds of
        []     -> pure (Nothing, bs)
        (q:qs) -> do g <- foldM andP q qs; pure (Just g, bs)

-- API ------------------------------------------------------------------

-- | Build a 'DFG' from a 'Program'. Also assigns super names first.
buildProgram :: Program -> DFG
buildProgram p0 =
  let Program decls = assignSuperNames (desugarProgram p0)
      tops = M.fromList [ (f, (ps, b)) | FunDecl f ps b <- decls, not (null ps) ]
      (_, st) = runBuild $ do
        Build $ modify (\s -> s { bsTopDecls = tops
                                 , bsRecFuns  = recursiveFuns decls
                                 , bsTypes    = topTypes p0 })
        mapM_ (\(FunDecl f ps body) -> insertB f (BLam ps body)) decls
        mapM_ buildZero decls
  in expandMoveRets st
  where
    retName f = f
    -- | Build and expose zero-argument functions as graph roots.
    buildZero (FunDecl f ps body) | null ps = do
      when (exprHasList body) (markListFun f)
      when (exprHasFloat body) (markFloatFun f)
      (v, p) <- withActive f (withEnv (do v <- goExpr body
                                          p <- asScalar v
                                          pure (v, p)))
      insertB f (BVal v)
      r <- retNodeId f
      setRetVal f p
      connectPlus p (InstPort r "0")
    buildZero _ = pure ()

-- função já construída?

-- | Has a return node for the given function @f@ already been emitted?
funBuilt :: Ident -> Build Bool
funBuilt f = Build $ gets $ \s -> any isRet (M.toList (dgNodes (bsGraph s)))
  where isRet (_, n) = case n of { NRet f' -> f' == f; _ -> False }

-- | Return node id for function @f@, creating it if needed.
retNodeId :: Ident -> Build NodeId
retNodeId = retNamed

-- | Ret node with this name, creating it if needed.
retNamed :: String -> Build NodeId
retNamed nm = Build $ do
  s <- get
  let found = [ nid
              | (nid, n) <- M.toList (dgNodes (bsGraph s))
              , case n of
                  NRet nm' -> nm' == nm
                  _        -> False
              ]
  case found of
    (h:_) -> pure h
    []    -> do
      nid <- lift freshId
      let g' = addNode nid (NRet nm) (bsGraph s)
      put s { bsGraph = g' }
      pure nid

-- evita reentrada recursiva

-- | Ensure a function @f@ is built at most once; guard against recursion.
ensureBuilt :: Ident -> [Ident] -> Expr -> Build ()
ensureBuilt f ps body = do
  done   <- funBuilt f
  active <- isActiveFun f
  if done || active
     then pure ()
     else do
       when (exprHasList body) (markListFun f)
       when (exprHasFloat body) (markFloatFun f)
       -- Create the ret node first so recursive call sites can target it.
       retN <- retNodeId f
       -- A function body runs in its own exec, so loops are allowed in it
       -- even when the call site sits inside a loop.
       inLoop0 <- Build $ gets bsInLoop
       Build $ modify (\s -> s { bsInLoop = False })
       lay <- funLayout f (length ps)
       case lay of
        Just (pshs, rsh) -> withActive f $ withNoGuard $ withEnv $ do
          (vs, _) <- foldM (\(acc, sl) sh -> do (v, sl') <- paramVal f sh sl
                                                pure (acc ++ [v], sl')) ([], 1) pshs
          zipWithM_ (\p v -> insertB p (BVal v)) ps vs
          res <- goExpr body
          ref <- argNode f 1
          ws  <- marshal (Just ref) rsh res
          emitResult f ws
        Nothing ->
         withActive f $ withNoGuard $ withEnv $ do
              forM_ (zip [0..] ps) $ \(i, v) -> do
                let slot = i + 1
                a <- argNode f slot
                insertB v (BVal (Scalar a))
              res <- goScalar body
              -- TALM ret: port 0 = result (callee exec), port 1 = return
              -- addresses from the retsnds of every call site.
              connectPlus res (InstPort retN "0")
       Build $ modify (\s -> s { bsInLoop = inLoop0 })
       pure ()

-- variável livre -> NArg

-- | Treat an unbound variable as a free 'NArg' input node.
freeVar :: Ident -> Build Port
freeVar x = do
  nid <- newNode x (NArg x)
  let p = out0 nid
  insertB x (BVal (Scalar p))
  pure p

-- detecta se um Port carrega float (por origem)

-- | Heuristically check if a port originates from floating-point ops/values.
-- Traces back through tag-management nodes (NIncTagI, NValTag, NAddI, NArg)
-- to find the originating operation.
portIsFloat :: Port -> Build Bool
portIsFloat p = Build $ gets $ \s -> isFloatNode s (pNode p)
  where
    isFloatNode s nid = case M.lookup nid (dgNodes (bsGraph s)) of
      Just NConstF{}         -> True
      Just NFAdd{}           -> True
      Just NFSub{}           -> True
      Just NFMul{}           -> True
      Just NFDiv{}           -> True
      Just NSuper{ superNum = k } -> k == builtinFMul || k == builtinFDiv
      Just (NRetSnd f _ _)   -> S.member f (bsFloatFuns s)
      Just (NRet f)          -> S.member (retFun f) (bsFloatFuns s)
      Just NIncTagI{}        -> tracePort0 s nid
      Just NValTag{}         -> tracePort0 s nid
      Just NAddI{}           -> tracePort0 s nid
      Just NArg{}            -> tracePort0 s nid
      _                      -> False
    tracePort0 s nid =
      case [ srcId | (srcId, _, d, dp) <- dgEdges (bsGraph s), d == nid, dp == "0" ] of
        (srcId:_) -> isFloatNode s srcId
        []        -> False

-- | Function a ret belongs to (@f__e0@, @f__r1@ .. are rets of @f@).
retFun :: String -> String
retFun = \case
  ('_':'_':_) -> []
  (c:cs)      -> c : retFun cs
  []          -> []

-- | Heuristically check if a port originates from list operations.
-- Traces through tag-management and steer nodes.
portIsList :: Port -> Build Bool
portIsList (SteerPort nid _) = Build $ gets $ \s ->
  -- Steer nodes: check aliases (the other branches may be lists)
  case M.lookup (nid, "t") (bsAliases s) of
    Just (p:_) -> isListNode s (pNode p)
    _          -> tracePort1 s nid
portIsList p = Build $ gets $ \s -> isListNode s (pNode p)

isListNode :: BuildS -> NodeId -> Bool
isListNode s nid = case M.lookup nid (dgNodes (bsGraph s)) of
  Just (NSuper { superNum = n }) -> n == 0  -- builtinListCons
  Just (NRetSnd f _ _)   -> S.member f (bsListFuns s)
  Just (NRet f)          -> S.member f (bsListFuns s)
  Just NSteer{}          -> tracePort1 s nid  -- steer: check input port 1
  Just NIncTagI{}        -> tracePort0 s nid
  Just NValTag{}         -> tracePort0 s nid
  Just NAddI{}           -> tracePort0 s nid
  Just NArg{}            -> tracePort0 s nid
  _                      -> False

tracePort0 :: BuildS -> NodeId -> Bool
tracePort0 s nid =
  case [ srcId | (srcId, _, d, dp) <- dgEdges (bsGraph s), d == nid, dp == "0" ] of
    (srcId:_) -> isListNode s srcId
    []        -> False

tracePort1 :: BuildS -> NodeId -> Bool
tracePort1 s nid =
  case [ srcId | (srcId, _, d, dp) <- dgEdges (bsGraph s), d == nid, dp == "1" ] of
    (srcId:_) -> isListNode s srcId
    []        -> False

-- | Is the current operation in a floating-point context?
isFloatContext :: Port -> Port -> Build Bool
isFloatContext a b = do
  af <- isFloatActive
  pa <- portIsFloat a
  pb <- portIsFloat b
  pure (af || pa || pb)

-- Expressões -----------------------------------------------------------

-- | Synthesize an expression into the graph and return its 'Val'.
goExpr :: Expr -> Build Val
goExpr = \case
  Var x -> do
    lookupB x >>= \case
      Just (BVal v) -> pure v
      Just (BLam ps body) ->
        if null ps
          then do v <- withEnv (goExpr body)
                  updateB x (BVal v)
                  pure v
          else Scalar <$> freeVar x
      Nothing -> Scalar <$> freeVar x

  Lit lit -> Scalar <$> litNode lit

  Lambda ps e ->
    withEnv $ do
      mapM_ (\v -> insertB v (BVal (Scalar (InstPort (-1) v)))) ps
      goExpr e

  If c t e -> do
    pc0 <- goScalar c
    pc <- boolify pc0
    pcTok <- guardToken pc
    baseK <- Build $ gets bsScopeK
    vtV <- withEnv (withGuard pc (goExpr t))
    kAfterT <- Build $ gets bsScopeK
    Build $ modify (\s -> s { bsScopeK = baseK })
    npc <- notP pc
    npcTok <- guardToken npc
    veV <- withEnv (withGuard npc (goExpr e))
    kAfterE <- Build $ gets bsScopeK
    Build $ modify (\s -> s { bsScopeK = max kAfterT kAfterE })
    if joinKind [vtV, veV] /= KScalar
      then joinVals [(pc, vtV), (npc, veV)]
      else do
        vt0 <- withGuard pc (asScalar vtV)
        vt <- alignExecTo pcTok vt0
        ve0 <- withGuard npc (asScalar veV)
        ve <- alignExecTo npcTok ve0
        stT <- newNode "if_t" (NSteer "")
        connect pc (InstPort stT "0")
        connect vt   (InstPort stT "1")
        let outT = SteerPort stT "t"

        stF <- newNode "if_f" (NSteer "")
        connect npc (InstPort stF "0")
        connect ve   (InstPort stF "1")
        let outF = SteerPort stF "t"

        registerAlias outT [outF]
        pure (Scalar outT)

  -- listas / tuplas: stream estático nativo (length-prefix)
  Cons a b -> do
    pa <- goScalar a
    vb <- goExpr b
    case vb of
      Stream c ps -> do c' <- addI c 1; pure (Stream c' (pa : ps))
      Scalar pb   -> Scalar <$> pairEnc pa pb
      DStream{}   -> dsCons pa vb
      VTup _      -> do pb <- asScalar vb; Scalar <$> pairEnc pa pb
  List xs  -> staticStream xs
  Tuple xs -> VTup <$> mapM goExpr xs

  Case scr alts -> compileCase scr alts

  Let decls body -> withEnv (mapM_ goDecl decls >> goExpr body)

  App f x -> let (g,args) = flattenApp (App f x) in goApp g args

  BinOp op l r -> do
    pl <- goScalar l
    pr <- goScalar r
    fctx <- isFloatContext pl pr
    Scalar <$> case op of
      Add | fctx      -> bin2 "fadd" (NFAdd "")  pl pr
          | otherwise -> bin2 "add"  (NAdd  "")  pl pr
      Sub | fctx      -> do ny <- fnegP pr            -- fsub = fadd(x, -y)
                            bin2 "fadd" (NFAdd "") pl ny
          | otherwise -> bin2 "sub"  (NSub  "")  pl pr
      Mul | fctx      -> callBuiltinSuper builtinFMul [pl, pr]
          | otherwise -> bin2 "mul"  (NMul  "")  pl pr
      Div | fctx      -> callBuiltinSuper builtinFDiv [pl, pr]
          | otherwise -> bin2 "div"  (NDiv  "")  pl pr
      Mod -> do
        qN <- bin2Node "div" (NDiv "") pl pr
        pure (out1Port qN)
      Eq  -> bin2 "equal" (NEqual "") pl pr
      Lt  -> bin2 "lthan" (NLThan "") pl pr
      Gt  -> bin2 "gthan" (NGThan "") pl pr
      And -> bin2 "band"  (NBand  "") pl pr
      Or  -> do s <- bin2Node "add" (NAdd "") pl pr
                z <- constI 0
                bin2 "gthan" (NGThan "") (out0 s) z
      Le  -> do lt <- bin2 "lthan" (NLThan "") pl pr
                eq <- bin2 "equal" (NEqual "")  pl pr
                orP lt eq
      Ge  -> do gt <- bin2 "gthan" (NGThan "") pl pr
                eq <- bin2 "equal" (NEqual "")  pl pr
                orP gt eq
      Neq -> do eq <- bin2 "equal" (NEqual "")  pl pr
                notP eq

  UnOp u e -> do
    pe <- goScalar e
    Scalar <$> case u of
      Neg -> do
        fl <- (||) <$> isFloatActive <*> portIsFloat pe
        if fl then fnegP pe
              else do z <- constI 0; bin2 "sub" (NSub "") z pe
      Not -> notP pe

  Super nm inputs _ -> do
    let args = if length inputs > 1 then tail inputs else inputs
    pIns <- mapM (\v -> goScalar (Var v)) args
    nid <- naryNode nm NSuper
             { nName     = ""
             , superNum  = superNumFromName nm
             , superOuts = 1
             , superSpec = False
             , superImm  = Nothing
             } pIns
    pure (Scalar (out0 nid))

-- | Static-length stream: count = N, payloads = element ports.
staticStream :: [Expr] -> Build Val
staticStream xs = do
  ps <- mapM goScalar xs
  c  <- constI (length ps)
  pure (Stream c ps)

-- Declarações ----------------------------------------------------------

-- | Insert a function lambda into the environment.
goDecl :: Decl -> Build ()
goDecl (FunDecl f ps body) = do
  Build $ modify (\s -> s { bsLocalFuns = S.insert f (bsLocalFuns s) })
  insertB f (BLam ps body)

-- Aplicação n-ária -----------------------------------------------------

-- | Flatten nested applications into @(head, args)@.
flattenApp :: Expr -> (Expr, [Expr])
flattenApp = \case
  App f x ->
    let (g, xs) = flattenApp f
    in (g, xs ++ [x])
  e -> (e, [])

-- | Mark a function as active while executing an action, then restore.
-- Resets the scope-level call counter so each function scope has its own k space.
withActive :: Ident -> Build a -> Build a
withActive f m = Build $ do
  s <- get
  let oldK = bsScopeK s
  put s{ bsActive = f : bsActive s, bsScopeK = 0 }
  r <- unBuild m
  s' <- get
  put s'{ bsActive = tail (bsActive s'), bsScopeK = oldK }
  pure r

-- taskId determinístico

-- | Deterministic task identifier derived from the function name.
funTaskId :: Ident -> Int
funTaskId _ident = 0

-- | Make all arguments of a call reach their callsnds in the same instance
-- order. TALM pairs the k-th execution of every callsnd in a callgroup (each
-- one counts its own executions into the exec tag), so if arguments of
-- different call instances arrive in different orders (e.g. one argument is
-- the result of a recursive call) values of different instances get paired.
-- A single sync token s = sum (a_i - a_i) = 0 fires once per instance after
-- all arguments are present; each callsnd receives a_i + s, so every callsnd
-- observes the instances in s's firing order. Integer add/sub on the raw
-- operand bits leaves floats and list handles unchanged.
syncArgs :: [Port] -> Build [Port]
syncArgs argv = case argv of
  []  -> pure []
  [_] -> pure argv
  _   -> do
    zs <- mapM (\a -> out0 <$> rawBin (NSub "") a a) argv
    s  <- foldM (\acc z -> out0 <$> rawBin (NAdd "") acc z) (head zs) (tail zs)
    mapM (\a -> out0 <$> rawBin (NAdd "") a s) argv
  where
    rawBin nd a b = do
      nid <- newNode "sync" nd
      connectPlus a (InstPort nid "0")
      connectPlus b (InstPort nid "1")
      pure nid

-- | Output port of a function's ret node that serves one call site.
-- Codegen prints it as @f.cg<N>_@; the FlowASM callgroup macro rewrites
-- @cg<N>_@ into that call site's callgroup index.
callgroupPort :: NodeId -> String
callgroupPort cg = "cg" ++ show cg ++ "_"

-- nó de argumento formal

-- | Ensure the formal argument node @fun#i@ exists and return its output port.
argNode :: String -> Int -> Build Port
argNode fun i = namedArg (fun ++ "#" ++ show i)

-- | Ensure an 'NArg' node with this name exists and return its output port.
namedArg :: String -> Build Port
namedArg nm = Build $ do
  s <- get
  let found = [ nid
              | (nid, n) <- M.toList (dgNodes (bsGraph s))
              , case n of
                  NArg nm' -> nm' == nm
                  _        -> False
              ]
  nid <- case found of
           (h:_) -> pure h
           []    -> do
             nid' <- lift freshId
             let g' = addNode nid' (NArg nm) (bsGraph s)
             put s { bsGraph = g' }
             pure nid'
  pure (out0 nid)

-- formal + alias para o real

-- | Apply a function or lambda to argument expressions.
goApp :: Expr -> [Expr] -> Build Val
goApp fun args = case fun of
  -- Built-in print variants (C-style):
  --   print x    → integer       prints xs   → string (ASCII list)
  --   printl xs  → list of int   printf x    → float
  --   printlf xs → list of float printmf xs  → matrix of floats
  Var p | p `elem` ["print","prints","printl","printf","printlf","printmf"]
        , length args == 1 -> do
    pArg <- goScalar (head args)
    let sn = case p of
               "print"   -> builtinPrint
               "prints"  -> builtinPrintStr
               "printl"  -> builtinPrintList
               "printf"  -> builtinPrintFloat
               "printlf" -> builtinPrintFloatList
               "printmf" -> builtinPrintFloatMatrix
               _         -> builtinPrint
    Scalar <$> callBuiltinSuper sn [pArg]

  -- Function call, TALM call protocol:
  --   callgroup(cg, f)              per call site; cg becomes its index
  --   callsnd f[i], arg_i, cg       exec := cg<<20 | call count, tag kept
  --   retsnd  r, arg_0, cg          value := caller exec (return address)
  --   ret     f, result, [r...]     routes to output port cg and restores
  --                                 the caller exec; consumers read f.cg
  -- Call instances are told apart by exec, so tags pass through unchanged.
  Var f -> do
    vals <- mapM goExpr args
    lowered <- lowerCall f vals
    case lowered of
      Just v  -> pure v
      Nothing -> talmCall f vals

  -- Lambda applied in place: beta-reduce by binding formals to the actuals.
  Lambda ps body -> do
    argv0 <- mapM goScalar args
    argv1 <- mapM guardIfNeeded argv0
    argv <- alignExecInputs argv1
    withEnv $ do
      forM_ (zip ps argv) $ \(v, a) -> insertB v (BVal (Scalar a))
      goExpr body

  _ -> do
    _ <- mapM goExpr args
    case args of
      [] -> Scalar <$> constI 0
      _  -> goExpr (last args)

-- | Plain TALM call of @f@ (arguments in scalar form).
talmCall :: Ident -> [Val] -> Build Val
talmCall f vals = funLayout f (length vals) >>= \case
  Just lay -> talmCallTyped f lay vals
  Nothing  -> talmCallPlain f vals

talmCallPlain :: Ident -> [Val] -> Build Val
talmCallPlain f vals = do
    argv0 <- mapM asScalar vals
    argv1 <- mapM guardIfNeeded argv0
    argv <- alignExecInputs argv1
    anyFloat <- or <$> mapM portIsFloat argv
    when anyFloat (markFloatFun f)

    lookupB f >>= \case
      Just (BLam ps body) -> ensureBuilt f ps body
      _                   -> pure ()

    let tid = funTaskId f
    cg <- newNode f (NCallGroup f)
    argvS <- syncArgs argv
    forM_ (zip [1..] argvS) $ \(slot, a) -> do
      let nm = f ++ "#" ++ show (slot :: Int)
      cs <- newNode nm (NCallSnd nm tid cg)
      connectPlus a (InstPort cs "0")
      ap <- argNode f slot
      case ap of
        InstPort nid _ -> connectPlus (out0 cs) (InstPort nid "0")
        _              -> pure ()

    retTok <- case argvS of
      (a0:_) -> pure a0
      []     -> constI 0
    rs <- newNode (f ++ "#0") (NRetSnd (f ++ "#0") tid cg)
    connectPlus retTok (InstPort rs "0")
    retN <- retNodeId f
    connectPlus (out0 rs) (InstPort retN "1")
    pure (Scalar (InstPort retN (callgroupPort cg)))

-- Laços nativos (recursão linear) ----------------------------------------
--
-- A call to a top-level function whose body is a linear self-recursion is
-- lowered at the call site to a TALM loop instead of a chain of calls:
--
-- * Tail recursion   f ps = if c then base else f args'   (either branch order)
--   Forward loop in the testewhile idiom: every parameter goes through
--   @inctag [init, feedback]@, the condition steers each one, the continue
--   side computes args' as feedback, the exit side evaluates base.
--
-- * List producer    f ps = if c then [] else e : f args'   (either order)
--   Same forward loop plus an iteration counter: the continue side emits e
--   (element k at tag t0+1+k) and its index; at exit the counter is the
--   count N, moved back to t0. The result is a 'DStream'.
--
-- * List consumer    f .. xs .. = case xs of [] -> base; (h:t) -> E[h, f .. t ..]
--   (xs a static stream or a DStream; the other parameters unchanged).
--   Element k is placed at tag t0+1+k. The accumulator starts as base at tag
--   t0+1+N and walks the tags down: each step does inctagi -1 and computes
--   E with the element that lives at that tag, so the result is exactly the
--   right fold. A remaining-count r (> 0 continues) is carried alongside.
--
-- Loops run in the caller's exec, at tags above the entry tag t0, and hand the
-- result back at tag t0. Loops are not nested: inside a loop body these calls
-- stay TALM calls (a fresh exec per call keeps the tags apart).
--
-- A call to a non-recursive top-level function with a stream argument is
-- inlined, so static streams never cross a call boundary as list supers.

-- | Shape of a tail-recursive body.
data TailShape = TailShape
  { tsCond       :: Expr
  , tsExitOnTrue :: Bool     -- ^ True: @if c then base else f ..@
  , tsBase       :: Expr
  , tsArgs       :: [Expr]   -- ^ arguments of the self-call
  }

-- | Shape of a list-producer body: @if c then [] else e : f args'@.
data ProdShape = ProdShape
  { prCond       :: Expr
  , prExitOnTrue :: Bool     -- ^ True: @if c then [] else ..@
  , prElem       :: Expr
  , prArgs       :: [Expr]
  }

recognizeProducer :: Ident -> [Ident] -> Expr -> Maybe ProdShape
recognizeProducer f ps = \case
  If c a b
    | occurs f c == 0, isNil a, Just (e, as) <- step b -> Just (ProdShape c True e as)
    | occurs f c == 0, isNil b, Just (e, as) <- step a -> Just (ProdShape c False e as)
  _ -> Nothing
  where
    isNil = \case { List [] -> True; _ -> False }
    step = \case
      Cons e r | occurs f e == 0
               , Just as <- selfCall f (length ps) r
               , all ((== 0) . occurs f) as -> Just (e, as)
      _ -> Nothing

-- | Shape of a list-consumer body.
data ConsShape = ConsShape
  { csIdx  :: Int            -- ^ position of the list parameter
  , csBase :: Expr           -- ^ result for []
  , csHead :: Maybe Ident    -- ^ head variable (Nothing for _)
  , csBody :: Expr           -- ^ E with the self-call replaced by 'recVar'
  }

-- | Name bound to the recursive result inside a consumer step.
recVar :: Ident
recVar = "rec#"

-- | Occurrences of variable @x@ in an expression (shadowing ignored).
occurs :: Ident -> Expr -> Int
occurs x = \case
  Var y          -> if x == y then 1 else 0
  Lit _          -> 0
  Lambda _ e     -> occurs x e
  If c t e       -> occurs x c + occurs x t + occurs x e
  Case s as      -> occurs x s + sum [ occurs x e | (_, e) <- as ]
  Let ds b       -> sum [ occurs x e | FunDecl _ _ e <- ds ] + occurs x b
  App a b        -> occurs x a + occurs x b
  BinOp _ l r    -> occurs x l + occurs x r
  UnOp _ e       -> occurs x e
  List es        -> sum (map (occurs x) es)
  Tuple es       -> sum (map (occurs x) es)
  Cons h t       -> occurs x h + occurs x t
  Super _ ins _  -> length (filter (== x) ins)

-- | Saturated self-call @f a1 .. an@?
selfCall :: Ident -> Int -> Expr -> Maybe [Expr]
selfCall f n e = case flattenApp e of
  (Var g, as) | g == f, length as == n -> Just as
  _                                    -> Nothing

recognizeTail :: Ident -> [Ident] -> Expr -> Maybe TailShape
recognizeTail f ps = \case
  If c a b
    | occurs f c == 0
    , Just as <- selfCall f (length ps) b, all ((== 0) . occurs f) as
    , occurs f a == 0 -> Just (TailShape c True a as)
    | occurs f c == 0
    , Just as <- selfCall f (length ps) a, all ((== 0) . occurs f) as
    , occurs f b == 0 -> Just (TailShape c False b as)
  _ -> Nothing

recognizeConsumer :: Ident -> [Ident] -> Expr -> Maybe ConsShape
recognizeConsumer f ps = \case
  Case (Var xs) alts
    | Just j <- M.lookup xs (M.fromList (zip ps [0..]))
    , Just (base, hd, tl, e) <- splitAlts alts
    , occurs f base == 0, occurs xs base == 0
    , occurs xs e == 0, occurs tl e == 1
    , Just e' <- replaceCall j tl e
    , occurs f e' == 0
    , maybe True (\h -> h /= tl && h `notElem` ps) hd
    , tl `notElem` ps
    -> Just (ConsShape j base hd e')
  _ -> Nothing
  where
    splitAlts alts = case alts of
      [(PList [], b), (PCons ph (PVar t), e)] -> withHead ph b t e
      [(PCons ph (PVar t), e), (PList [], b)] -> withHead ph b t e
      _ -> Nothing
    withHead ph b t e = case ph of
      PVar h    -> Just (b, Just h, t, e)
      PWildcard -> Just (b, Nothing, t, e)
      _         -> Nothing
    -- Replace the single self-call f p1 .. t .. pn by recVar.
    replaceCall j tl = go
      where
        ok as = and [ case a of
                        Var v -> if i == j then v == tl else v == ps !! i
                        _     -> False
                    | (i, a) <- zip [0..] as ]
        go e = case selfCall f (length ps) e of
          Just as | ok as -> Just (Var recVar)
          Just _          -> Nothing
          Nothing -> case e of
            Var _         -> Just e
            Lit _         -> Just e
            If c t x      -> If <$> go c <*> go t <*> go x
            BinOp o l r   -> BinOp o <$> go l <*> go r
            UnOp o x      -> UnOp o <$> go x
            App a b       -> App <$> go a <*> go b
            Cons h t      -> Cons <$> go h <*> go t
            List es       -> List <$> mapM go es
            Tuple es      -> Tuple <$> mapM go es
            Case sc as    -> Case <$> go sc <*> mapM (\(pt, x) -> (,) pt <$> go x) as
            Let ds b
              | all (\(FunDecl _ _ x) -> occurs f x == 0) ds -> Let ds <$> go b
            _             -> if occurs f e == 0 then Just e else Nothing

-- | Top-level functions that lie on a call cycle (self or mutual recursion).
recursiveFuns :: [Decl] -> S.Set Ident
recursiveFuns decls =
  S.fromList [ f | f <- M.keys calls, f `S.member` reach f ]
  where
    names = S.fromList [ f | FunDecl f _ _ <- decls ]
    calls = M.fromList [ (f, S.filter (\g -> occurs g b > 0) names) | FunDecl f _ b <- decls ]
    reach f = go S.empty (S.toList (M.findWithDefault S.empty f calls))
      where
        go seen [] = seen
        go seen (g:gs)
          | g `S.member` seen = go seen gs
          | otherwise = go (S.insert g seen)
                           (S.toList (M.findWithDefault S.empty g calls) ++ gs)

-- | Lower a call to a loop / inline it when its shape allows; Nothing = TALM call.
lowerCall :: Ident -> [Val] -> Build (Maybe Val)
lowerCall f vals = do
  st <- Build get
  let isLocal = f `S.member` bsLocalFuns st
      mdecl   = M.lookup f (bsTopDecls st)
      isRec   = f `S.member` bsRecFuns st
      hasStream = any isStreamVal vals
      -- With types known, loops only for scalar state and stream-free bodies
      -- (a stream inside a loop body would put its elements on the tags of
      -- later iterations).
      tys     = bsTypes st
      known   = not (M.null tys)
      (pTys, rTy) = case M.lookup f tys of
                      Just (Sem.TFun as r) -> (as, r)
                      _                    -> ([], Sem.TInt)
      scalarT t = shapeOfType t == ShS
      lf      = listFree tys
      elemScalar = \case { Sem.TList t -> scalarT t; _ -> False }
      tailOK ts = not known || ( all scalarT pTys && scalarT rTy
                               && all lf (tsCond ts : tsBase ts : tsArgs ts) )
      consOK cs = not known || ( and [ scalarT t | (k, t) <- zip [0 ..] pTys, k /= csIdx cs ]
                               && scalarT rTy && lf (csBase cs) && lf (csBody cs)
                               && maybe False elemScalar (listToMaybe (drop (csIdx cs) pTys)) )
      prodOK pr = not known || ( all scalarT pTys && elemScalar rTy
                               && all lf (prCond pr : prElem pr : prArgs pr) )
  case mdecl of
    Just (ps, body)
      | not isLocal, length ps == length vals, not (bsInLoop st) ->
          case ( recognizeTail f ps body, recognizeConsumer f ps body
               , recognizeProducer f ps body ) of
            (Just ts, _, _) | tailOK ts -> Just <$> tailLoop ps ts vals
            (_, Just cs, _) | consOK cs, Stream _ xs <- vals !! csIdx cs ->
                                Just <$> consumerLoop ps cs (Left xs) vals
            (_, Just cs, _) | consOK cs, DStream c e _ <- vals !! csIdx cs ->
                                Just <$> consumerLoop ps cs (Right (c, e)) vals
            (_, _, Just pr) | prodOK pr -> Just <$> producerLoop ps pr vals
            _ | not isRec && hasStream -> Just <$> inlineCall ps body vals
            _ -> pure Nothing
      | not isLocal, length ps == length vals, not isRec, hasStream ->
          Just <$> inlineCall ps body vals
    _ -> pure Nothing
  where
    isStreamVal = \case { Scalar{} -> False; _ -> True }

-- | Gate a value by the current guard (all of its ports).
guardVal :: Val -> Build Val
guardVal = \case
  Scalar p    -> Scalar <$> guardIfNeeded p
  Stream c ps -> Stream <$> guardIfNeeded c <*> mapM guardIfNeeded ps
  -- Elements live at other tags; gating the count (and hence any loop that
  -- reads them) is enough.
  DStream c e i -> (\c' -> DStream c' e i) <$> guardIfNeeded c
  VTup vs       -> VTup <$> mapM guardVal vs

-- | Inline a non-recursive function: bind the parameters to the actual values.
inlineCall :: [Ident] -> Expr -> [Val] -> Build Val
inlineCall ps body vals = do
  vs <- mapM guardVal vals
  withEnv $ do
    forM_ (zip ps vs) $ \(p, v) -> insertB p (BVal v)
    goExpr body

-- | Run @m@ as a loop body: constants align to @tok@ (via the guard slot,
-- whose value 1 also lets guarded calls through) and loops do not nest.
inLoopCtx :: Port -> Build a -> Build a
inLoopCtx tok m = do
  s0 <- Build get
  Build $ modify (\s -> s { bsGuard = Just tok, bsInLoop = True })
  r <- m
  Build $ modify (\s -> s { bsGuard = bsGuard s0, bsInLoop = bsInLoop s0 })
  pure r

-- | Raw single-input node.
node1 :: String -> DNode -> Port -> Build Port
node1 lbl nd p = do
  nid <- newNode lbl nd
  connectPlus p (InstPort nid "0")
  pure (out0 nid)

-- | Raw two-input node.
node2 :: String -> DNode -> Port -> Port -> Build Port
node2 lbl nd a b = do
  nid <- newNode lbl nd
  connectPlus a (InstPort nid "0")
  connectPlus b (InstPort nid "1")
  pure (out0 nid)

-- | Merge several producers into one port (identity addi with a source list).
mergeP :: String -> [Port] -> Build NodeId
mergeP lbl srcs = do
  nid <- newNode lbl (NAddI "" 0)
  mapM_ (\p -> connectPlus p (InstPort nid "0")) srcs
  pure nid

-- | Steer @v@ on @c@: (true side, false side).
steerP :: Port -> Port -> Build (Port, Port)
steerP c v = do
  sid <- newNode "loop_steer" (NSteer "")
  connectPlus c (InstPort sid "0")
  connectPlus v (InstPort sid "1")
  pure (SteerPort sid "t", SteerPort sid "f")

tagValP :: Port -> Build Port
tagValP = node1 "tagval" (NTagVal "")

-- | valtag: @v@ moved to the tag given by the value of @t@ (same tag/exec).
valTagP :: Port -> Port -> Build Port
valTagP = node2 "valtag" (NValTag "")

incTagIP :: Int -> Port -> Build Port
incTagIP k = node1 ("inctagi_" ++ show k) (NIncTagI "" k)

-- | Tail recursion as a forward loop (testewhile idiom).
tailLoop :: [Ident] -> TailShape -> [Val] -> Build Val
tailLoop ps ts vals = do
  argv0 <- mapM asScalar vals
  argv1 <- mapM guardIfNeeded argv0
  inits <- alignExecInputs argv1
  let ref = head inits
  entry <- tagValP ref                       -- t0, carried to restore the tag
  -- headers: inctag [init, feedback]
  hdrs <- mapM (\_ -> newNode "loop_inctag" (NIncTag "")) (inits ++ [entry])
  zipWithM_ (\h p -> connectPlus p (InstPort h "0")) hdrs (inits ++ [entry])
  let hps     = map out0 hdrs
      hParams = init hps
      hEntry  = last hps
  tokH <- constFrom (head hps) 1
  c <- inLoopCtx tokH $ withEnv $ do
         zipWithM_ (\p h -> insertB p (BVal (Scalar h))) ps hParams
         goScalar (tsCond ts) >>= boolify
  steered <- mapM (steerP c) hps
  let (contS, exitS) = unzip [ if tsExitOnTrue ts then (f', t') else (t', f')
                             | (t', f') <- steered ]
  -- continue: feedback = args'
  tokC <- constFrom (head contS) 1
  nexts <- inLoopCtx tokC $ withEnv $ do
             zipWithM_ (\p v -> insertB p (BVal (Scalar v))) ps (init contS)
             mapM goScalar (tsArgs ts)
  zipWithM_ (\h n -> connectPlus n (InstPort h "0")) hdrs (nexts ++ [last contS])
  -- exit: base, moved back to the entry tag
  tokE <- constFrom (head exitS) 1
  res <- inLoopCtx tokE $ withEnv $ do
           zipWithM_ (\p v -> insertB p (BVal (Scalar v))) ps (init exitS)
           goScalar (tsBase ts)
  Scalar <$> valTagP res (last exitS)

-- | List producer as a forward loop yielding a 'DStream'.
producerLoop :: [Ident] -> ProdShape -> [Val] -> Build Val
producerLoop ps pr vals = do
  argv0 <- mapM asScalar vals
  argv1 <- mapM guardIfNeeded argv0
  inits <- alignExecInputs argv1
  let ref = head inits
  entry <- tagValP ref
  j0    <- constFrom ref 0
  let carried = inits ++ [entry, j0]
  hdrs <- mapM (\_ -> newNode "loop_inctag" (NIncTag "")) carried
  zipWithM_ (\h p -> connectPlus p (InstPort h "0")) hdrs carried
  let hps = map out0 hdrs
      np  = length inits
  tokH <- constFrom (head hps) 1
  c <- inLoopCtx tokH $ withEnv $ do
         zipWithM_ (\p h -> insertB p (BVal (Scalar h))) ps (take np hps)
         goScalar (prCond pr) >>= boolify
  steered <- mapM (steerP c) hps
  let (contS, exitS) = unzip [ if prExitOnTrue pr then (f', t') else (t', f')
                             | (t', f') <- steered ]
      [entC, jC] = drop np contS
      [entE, jE] = drop np exitS
  tokC <- constFrom (head contS) 1
  (el, nexts) <- inLoopCtx tokC $ withEnv $ do
                   zipWithM_ (\p v -> insertB p (BVal (Scalar v))) ps (take np contS)
                   e  <- goScalar (prElem pr)
                   ns <- mapM goScalar (prArgs pr)
                   pure (e, ns)
  elA <- alignExecTo jC el
  j'  <- addI jC 1
  zipWithM_ (\h n -> connectPlus n (InstPort h "0")) hdrs (nexts ++ [entC, j'])
  cnt <- valTagP jE entE
  pure (DStream cnt elA jC)

-- | head of a DStream: element 0, moved to the owner tag t0.
dsHead :: Val -> Build Port
dsHead = \case
  DStream _ e i -> do
    z  <- constFrom i 0
    is0 <- node2 "equal" (NEqual "") i z
    (eT, _) <- steerP is0 e
    incTagIP (-1) eT
  v -> asScalar v

-- | tail of a DStream: elements 1.. shifted down one tag, indices minus one.
dsTail :: Val -> Build Val
dsTail = \case
  DStream c e i -> do
    z   <- constFrom i 0
    gt0 <- node2 "gthan" (NGThan "") i z
    (eT, _) <- steerP gt0 e
    (iT, _) <- steerP gt0 i
    e' <- incTagIP (-1) eT
    i0 <- incTagIP (-1) iT
    i' <- subI i0 1
    c' <- subI c 1
    pure (DStream c' e' i')
  v -> pure v

-- | x : DStream, natively: new element at index 0, the rest shifted up.
dsCons :: Port -> Val -> Build Val
dsCons x = \case
  DStream c e i -> do
    xA <- alignExecTo c x
    t0 <- tagValP c
    t1 <- addI t0 1
    x1 <- valTagP xA t1
    z  <- constFrom c 0
    z1 <- valTagP z t1
    eUp <- incTagIP 1 e
    iUp <- incTagIP 1 i >>= \p -> addI p 1
    e' <- out0 <$> mergeP "dcons_elem" [x1, eUp]
    i' <- out0 <$> mergeP "dcons_idx" [z1, iUp]
    c' <- addI c 1
    pure (DStream c' e' i')
  v -> do p <- asScalar v; Scalar <$> pairEnc x p

-- | List consumer as a backward loop over the tags; the list is either a
-- static stream (Left payloads) or a DStream (Right (count, elements)).
consumerLoop :: [Ident] -> ConsShape -> Either [Port] (Port, Port) -> [Val] -> Build Val
consumerLoop ps cs src vals = do
  let j    = csIdx cs
      invI = [ i | i <- [0 .. length ps - 1], i /= j ]
  invs0 <- mapM (\i -> asScalar (vals !! i)) invI
  invs1 <- mapM guardIfNeeded invs0
  (statics, dyn) <- case src of
    Left xs       -> do xs' <- mapM guardIfNeeded xs; pure (xs', Nothing)
    Right (c, e)  -> do c' <- guardIfNeeded c; pure ([c'], Just e)
  ins <- alignExecInputs (invs1 ++ statics)
  let (invs, rest) = splitAt (length invs1) ins
  ref <- case ins of
           (r:_) -> pure r
           []    -> constI 0
  -- base at the entry tag t0
  tok0 <- constFrom ref 1
  baseV <- inLoopCtx tok0 $ withEnv $ do
             zipWithM_ (\i v -> insertB (ps !! i) (BVal (Scalar v))) invI invs
             goScalar (csBase cs)
  baseA <- alignExecTo ref baseV
  (cnt, elems) <- case dyn of
    Just e -> pure (head rest, Just e)
    Nothing -> do
      t0 <- tagValP ref
      t1 <- addI t0 1
      eps <- forM (zip [0 :: Int ..] rest) $ \(k, p) -> do
               tk <- if k == 0 then pure t1 else addI t1 k
               valTagP p tk
      n  <- constFrom ref (length rest)
      em <- if null eps then pure Nothing else Just . out0 <$> mergeP "loop_elem" eps
      pure (n, em)
  let step dInvs h acc = withEnv $ do
        zipWithM_ (\i v -> insertB (ps !! i) (BVal (Scalar v))) invI dInvs
        insertB recVar (BVal (Scalar acc))
        case csHead cs of
          Just hv -> insertB hv (BVal (Scalar h))
          Nothing -> pure ()
        goScalar (csBody cs)
  Scalar <$> case elems of
    Just e  -> backFold ref invs cnt e baseA step
    Nothing -> pure baseA                       -- static [] : just the base

-- | Backward fold over tag-indexed elements (element k at tag t0+1+k, with
-- t0 the tag of @ref@): the accumulator starts as @base@ at tag t0+1+N and
-- walks the tags down with inctagi -1, combining with the element found at
-- each tag via @step@; a remaining-count (> 0 continues) is carried along,
-- as are the loop invariants @invs@. The result comes back at tag t0.
backFold :: Port -> [Port] -> Port -> Port -> Port
         -> ([Port] -> Port -> Port -> Build Port) -> Build Port
backFold ref invs cnt elems base step = do
  t0 <- tagValP ref
  t1 <- addI t0 1
  tN <- bin2 "add" (NAdd "") t1 cnt
  starts <- mapM (\v -> valTagP v tN) (base : cnt : invs)
  hdrs <- mapM (\p -> mergeP "loop_hdr" [p]) starts
  let hps = map out0 hdrs
      hR  = hps !! 1
  zR <- constFrom hR 0
  c  <- node2 "gthan" (NGThan "") hR zR
  steered <- mapM (steerP c) hps
  decs <- mapM (incTagIP (-1) . fst) steered
  let (dAcc : dR : dInvs) = decs
  tokD <- constFrom dAcc 1
  acc' <- inLoopCtx tokD (step dInvs elems dAcc)
  r'   <- subI dR 1
  zipWithM_ (\h p -> connectPlus p (InstPort h "0")) hdrs (acc' : r' : dInvs)
  -- exit (count 0 left) happens at tag t0+1: move back to t0
  incTagIP (-1) (snd (head steered))

-- Streams across calls ----------------------------------------------------
--
-- A top-level function whose inferred type mentions lists or tuples gets a
-- typed call layout. Each parameter and the result is flattened into wires:
-- a scalar is one wire, a list is a DStream wire, a tuple is its components.
--
-- * Scalar wires (and the count of every DStream wire) go through the usual
--   callsnd/retsnd/ret protocol.
-- * Elements and indices cannot go through callsnd: a callsnd counts every
--   token it sends, so N elements would land in N different execs. They are
--   moved with ret instead, which sets the exec from its control operand:
--   @ret W, elem, ctl@ puts elem in exec ctl.value at the same tag.
--   Call side: the callee exec X is obtained as a value in the caller exec
--   ('execValue'), spread over the element tags ('spreadP') and used as the
--   control of the moving rets; their outputs feed the callee's element
--   input. Return side: the return address (the caller exec, which the
--   retsnd delivers) is spread the same way and the callee's element rets
--   route by call site like any ret (@f__e<j>.cg@).
-- Positions stay in tags (element k at tag t0+1+k on both sides); execs keep
-- call instances apart.

-- | Representation a value takes at a call boundary.
data VShape = ShS | ShL | ShT [VShape]
  deriving (Eq)

shapeOfType :: Sem.Type -> VShape
shapeOfType = \case
  Sem.TList _   -> ShL
  Sem.TTuple ts -> ShT (map shapeOfType ts)
  _             -> ShS

typeHasList :: Sem.Type -> Bool
typeHasList = \case
  Sem.TList _   -> True
  Sem.TTuple ts -> any typeHasList ts
  Sem.TFun as r -> any typeHasList (r : as)
  _             -> False

-- | Typed call layout of a top-level function (Nothing: all scalar, plain call).
funLayout :: Ident -> Int -> Build (Maybe ([VShape], VShape))
funLayout f n = do
  st <- Build get
  if f `S.member` bsLocalFuns st || not (M.member f (bsTopDecls st))
    then pure Nothing
    else case M.lookup f (bsTypes st) of
      Just (Sem.TFun as r) | length as == n ->
        let pshs = map shapeOfType as
            rsh  = shapeOfType r
        in pure (if all (== ShS) (rsh : pshs) then Nothing else Just (pshs, rsh))
      _ -> pure Nothing

-- | One wire of a flattened value.
data Wire = WS Port | WD Port Port Port

wireScalar :: Wire -> Port
wireScalar = \case
  WS p     -> p
  WD c _ _ -> c

-- | A port of the value's own context (tag/exec).
valRef :: Val -> Port
valRef = \case
  Scalar p      -> p
  Stream c _    -> c
  DStream c _ _ -> c
  VTup (v:_)    -> valRef v
  VTup []       -> InstPort (-1) "0"

valPorts :: Val -> [Port]
valPorts = \case
  Scalar p      -> [p]
  Stream c ps   -> ps ++ [c]
  DStream c _ _ -> [c]
  VTup vs       -> concatMap valPorts vs

firstNonConst :: [Port] -> Build (Maybe Port)
firstNonConst ps = do
  cs <- mapM getConstI ps
  pure (listToMaybe [ p | (p, Nothing) <- zip ps cs, pNode p /= (-1) ])

-- | Context reference for aligning constants: the guard, else a value port.
ctxRef :: [Val] -> Build (Maybe Port)
ctxRef vs = do
  mg <- Build $ gets bsGuard
  case mg of
    Just g  -> pure (Just g)
    Nothing -> firstNonConst (concatMap valPorts vs)

alignC :: Maybe Port -> Port -> Build Port
alignC Nothing p  = pure p
alignC (Just r) p = do
  mc <- getConstI p
  case mc of
    Just k  -> constFrom r k
    Nothing -> pure p

-- | A port that never fires (elements of an empty stream).
neverP :: Port -> Build Port
neverP r = do z <- constFrom r 0; fst <$> steerP z r

freshName :: String -> Build String
freshName pre = Build (lift freshId) >>= \n -> pure (pre ++ show n)

-- | Any list value as a DStream (count, elements, indices).
toDStream :: Maybe Port -> Val -> Build (Port, Port, Port)
toDStream ref v = case v of
  DStream c e i -> pure (c, e, i)
  Stream c [] -> do
    c' <- alignC ref c
    nv <- neverP c'
    pure (c', nv, nv)
  Stream c ps -> do
    r <- maybe (firstNonConst (ps ++ [c])) (pure . Just) ref
    ps' <- mapM (alignC r) ps
    c'  <- alignC r c
    t0  <- maybe (withNoGuard (constI 0)) tagValP r
    t1  <- addI t0 1
    eis <- forM (zip [0 :: Int ..] ps') $ \(k, p) -> do
             tk <- if k == 0 then pure t1 else addI t1 k
             e  <- valTagP p tk
             ik <- constFrom p k
             i  <- valTagP ik tk
             pure (e, i)
    em <- mergeP "ds_elem" (map fst eis)
    im <- mergeP "ds_idx" (map snd eis)
    pure (c', out0 em, out0 im)
  Scalar p -> alignC ref p >>= pairToDStream
  VTup _   -> asScalar v >>= pairToDStream

-- | Walk a pair-encoded list (list supers) into a DStream: forward loop that
-- emits head at tag t0+1+k with its index k; at nil the count goes back to t0.
pairToDStream :: Port -> Build (Port, Port, Port)
pairToDStream p = do
  entry <- tagValP p
  j0    <- constFrom p 0
  let inits = [p, entry, j0]
  hdrs <- mapM (\_ -> newNode "p2s_inctag" (NIncTag "")) inits
  zipWithM_ (\h x -> connectPlus x (InstPort h "0")) hdrs inits
  let hps = map out0 hdrs
  isn <- callBuiltinSuper builtinListIsNil [head hps]
  steered <- mapM (steerP isn) hps
  let [(_, cK), (eX, eK), (jX, jK)] = steered
  el  <- fstDec cK
  nxt <- sndDec cK
  j'  <- addI jK 1
  zipWithM_ (\h x -> connect x (InstPort h "0")) hdrs [nxt, eK, j']
  cnt <- valTagP jX eX
  pure (cnt, el, jK)

-- | Value @v@ (tag t0) replicated at tags t0+1 .. t0+n, n the count @c@ (tag t0).
spreadP :: Port -> Port -> Build Port
spreadP v c = do
  hV <- newNode "spread_v" (NIncTag "")
  hR <- newNode "spread_r" (NIncTag "")
  connectPlus v (InstPort hV "0")
  connectPlus c (InstPort hR "0")
  z    <- constFrom (out0 hR) 0
  more <- node2 "gthan" (NGThan "") (out0 hR) z
  (vT, _) <- steerP more (out0 hV)
  (rT, _) <- steerP more (out0 hR)
  r' <- subI rT 1
  connect vT (InstPort hV "0")
  connect r' (InstPort hR "0")
  pure vT

-- | Gate a DStream by the current guard: count and every element.
gateDS :: Val -> Build Val
gateDS v = case v of
  DStream c e i -> do
    mg <- Build $ gets bsGuard
    case mg of
      Nothing -> pure v
      Just _  -> do
        c'   <- guardIfNeeded c
        one  <- constFrom c' 1
        pass <- spreadP one c'
        (e', _) <- steerP pass e
        (i', _) <- steerP pass i
        pure (DStream c' e' i')
  _ -> pure v

-- | How branch values are joined.
data JoinKind = KScalar | KDS | KTup Int
  deriving (Eq)

joinKind :: [Val] -> JoinKind
joinKind vs
  | Just n <- tupArity                       = KTup n
  | any isDS vs, not (any isTup vs)          = KDS
  | otherwise                                = KScalar
  where
    isDS  = \case { DStream{} -> True; _ -> False }
    isTup = \case { VTup _ -> True; _ -> False }
    tupArity = case [ length ws | VTup ws <- vs ] of
      ns@(n:_) | length ns == length vs, all (== n) ns -> Just n
      _ -> Nothing

-- | Join branch values, each built under its guard. Scalars are steered by the
-- guard token; DStreams are gated (count and elements) and merged, so only the
-- taken branch's tokens reach the result.
joinVals :: [(Port, Val)] -> Build Val
joinVals brs = case joinKind (map snd brs) of
  KTup n -> VTup <$> forM [0 .. n - 1] (\k ->
              joinVals [ (g, comp k v) | (g, v) <- brs ])
  KDS -> do
    parts <- forM brs $ \(g, v) -> withGuard g $ do
      ref <- Build $ gets bsGuard
      v1  <- case v of
               Scalar p -> Scalar <$> guardIfNeeded p
               _        -> pure v
      (c, e, i) <- toDStream ref v1
      gateDS (DStream c e i)
    cm <- mergeP "join_cnt"  [ c | DStream c _ _ <- parts ]
    em <- mergeP "join_elem" [ e | DStream _ e _ <- parts ]
    im <- mergeP "join_idx"  [ i | DStream _ _ i <- parts ]
    pure (DStream (out0 cm) (out0 em) (out0 im))
  KScalar -> do
    outs <- forM brs $ \(g, v) -> do
      p0  <- withGuard g (asScalar v)
      p   <- alignExecTo g p0
      tok <- guardToken g
      sid <- newNode "steer" (NSteer "")
      connect tok (InstPort sid "0")
      connect p   (InstPort sid "1")
      pure (SteerPort sid "t")
    case outs of
      (h:rest) -> registerAlias h rest >> pure (Scalar h)
      []       -> Scalar <$> falseP
  where
    comp k = \case
      VTup ws -> ws !! k
      w       -> w

-- | Flatten a value into wires following a shape.
marshal :: Maybe Port -> VShape -> Val -> Build [Wire]
marshal ref sh v = case sh of
  ShS -> do p <- asScalar v; p' <- alignC ref p; pure [WS p']
  ShL -> do (c, e, i) <- toDStream ref v; pure [WD c e i]
  ShT shs -> do
    comps <- case v of
      VTup ws     | length ws == length shs -> pure ws
      Stream _ ps | length ps == length shs -> pure (map Scalar ps)
      _ -> do p <- asScalar v; map Scalar <$> tupleComps p (length shs)
    concat <$> zipWithM (marshal ref) shs comps
  where
    tupleComps _ 0 = pure []
    tupleComps p 1 = (: []) <$> fstDec p
    tupleComps p n = do hd <- fstDec p; tl <- sndDec p; (hd :) <$> tupleComps tl (n - 1)

-- | Is each wire of a shape a stream?
flatShape :: VShape -> [Bool]
flatShape = \case
  ShS     -> [False]
  ShL     -> [True]
  ShT shs -> concatMap flatShape shs

-- | Name of the ret carrying result wire @j@ (wire 0 keeps the function name).
retNameJ :: Ident -> Int -> String
retNameJ f 0 = f
retNameJ f j = f ++ "__r" ++ show j

-- | Callee parameter value of a shape, starting at formal slot @slot@.
paramVal :: Ident -> VShape -> Int -> Build (Val, Int)
paramVal f sh slot = case sh of
  ShS -> do a <- argNode f slot; pure (Scalar a, slot + 1)
  ShL -> do
    c <- argNode f slot
    e <- namedArg (f ++ "#e" ++ show slot)
    i <- namedArg (f ++ "#i" ++ show slot)
    pure (DStream c e i, slot + 1)
  ShT shs -> do
    (vs, s') <- foldM (\(acc, sl) sh' -> do (v, sl') <- paramVal f sh' sl
                                            pure (acc ++ [v], sl')) ([], slot) shs
    pure (VTup vs, s')

-- | Caller-side result value of a shape, read from output @cgp@ of the rets.
resultVal :: Ident -> String -> VShape -> Int -> Build (Val, Int)
resultVal f cgp sh j = case sh of
  ShS -> do r <- retNamed (retNameJ f j); pure (Scalar (InstPort r cgp), j + 1)
  ShL -> do
    r  <- retNamed (retNameJ f j)
    re <- retNamed (f ++ "__e" ++ show j)
    ri <- retNamed (f ++ "__i" ++ show j)
    pure (DStream (InstPort r cgp) (InstPort re cgp) (InstPort ri cgp), j + 1)
  ShT shs -> do
    (vs, j') <- foldM (\(acc, k) sh' -> do (v, k') <- resultVal f cgp sh' k
                                           pure (acc ++ [v], k')) ([], j) shs
    pure (VTup vs, j')

-- | Callee side: connect the result wires to their rets.
emitResult :: Ident -> [Wire] -> Build ()
emitResult f ws = forM_ (zip [0 ..] ws) $ \(j, w) -> do
  r <- retNamed (retNameJ f j)
  connectPlus (wireScalar w) (InstPort r "0")
  case w of
    WD c e i -> do
      ra  <- namedArg (f ++ "#ra")
      ctl <- spreadP ra c
      re  <- retNamed (f ++ "__e" ++ show j)
      ri  <- retNamed (f ++ "__i" ++ show j)
      connectPlus e (InstPort re "0"); connect ctl (InstPort re "1")
      connectPlus i (InstPort ri "0"); connect ctl (InstPort ri "1")
    WS _ -> pure ()

-- | The callee exec of a call instance, as a value in the caller exec, at the
-- tag of @tok@ (the token that feeds the first callsnd). A callsnd in the
-- same callgroup, fed by @tok@, runs in step with the argument callsnds and
-- so lands in the callee exec X; two retsnds of a private callgroup turn it
-- and @tok@ into (value X) and (value caller exec) in a common exec, and a
-- ret of those two yields X in the caller exec.
execValue :: NodeId -> Port -> Build Port
execValue cg tok = do
  xa <- freshName "xa"
  a  <- newNode xa (NCallSnd xa 0 cg)
  connectPlus tok (InstPort a "0")
  zn <- freshName "xv"
  q  <- newNode zn (NCallGroup zn)
  b  <- newNode "xb" (NRetSnd "xb" 0 q)
  connect (out0 a) (InstPort b "0")
  c  <- newNode "xc" (NRetSnd "xc" 0 q)
  connectPlus tok (InstPort c "0")
  d  <- newNode zn (NRet zn)
  connect (out0 b) (InstPort d "0")
  connect (out0 c) (InstPort d "1")
  pure (InstPort d (callgroupPort q))

-- | Move @src@ to the exec given by @ctl@ (same tag) and feed @dst@. The ret
-- picks its output port from the caller exec's callgroup index, which is
-- only known at run time; the post-pass in 'buildProgram' adds the other
-- ports ('expandMoveRets').
moveRet :: Maybe Ident -> Port -> Port -> Port -> Build ()
moveRet owner src ctl dst = do
  nm <- freshName "mv"
  d  <- newNode nm (NRet nm)
  connectPlus src (InstPort d "0")
  connect ctl (InstPort d "1")
  Build $ modify (\s -> s { bsMoveRets = (d, owner) : bsMoveRets s })
  connect (InstPort d "0") dst

-- | Every move ret serves the exec of its owner function, whose callgroup
-- index can be any of 0 .. (number of callgroups of the owner) - 1.
expandMoveRets :: BuildS -> DFG
expandMoveRets st = foldr addEdge g extra
  where
    g = bsGraph st
    cgCount = M.fromListWith (+) [ (nName n, 1 :: Int) | n@NCallGroup{} <- M.elems (dgNodes g) ]
    extra = [ (d, show k, dst, dp)
            | (d, owner) <- bsMoveRets st
            , let nP = maybe 1 (\o -> max 1 (M.findWithDefault 0 o cgCount)) owner
            , (s, sp, dst, dp) <- dgEdges g, s == d, sp == "0"
            , k <- [1 .. nP - 1] ]

-- | TALM call with a typed layout (streams and tuples cross natively).
talmCallTyped :: Ident -> ([VShape], VShape) -> [Val] -> Build Val
talmCallTyped f (pshs, rsh) vals = do
  ref0  <- ctxRef vals
  wires <- concat <$> zipWithM (marshal ref0) pshs vals
  argv1 <- mapM (guardIfNeeded . wireScalar) wires
  argv  <- alignExecInputs argv1
  anyFloat <- or <$> mapM portIsFloat argv
  when anyFloat (markFloatFun f)
  lookupB f >>= \case
    Just (BLam ps body) -> ensureBuilt f ps body
    _                   -> pure ()
  cg <- newNode f (NCallGroup f)
  argvS <- syncArgs argv
  forM_ (zip [1..] argvS) $ \(slot, a) -> do
    let nm = f ++ "#" ++ show (slot :: Int)
    cs <- newNode nm (NCallSnd nm 0 cg)
    connectPlus a (InstPort cs "0")
    ap <- argNode f slot
    case ap of
      InstPort nid _ -> connectPlus (out0 cs) (InstPort nid "0")
      _              -> pure ()
  retTok <- case argvS of
    (a0:_) -> pure a0
    []     -> constI 0
  rs <- newNode (f ++ "#0") (NRetSnd (f ++ "#0") 0 cg)
  connectPlus retTok (InstPort rs "0")
  let flat = flatShape rsh
  forM_ (zip [0 ..] flat) $ \(j, _) -> do
    r <- retNamed (retNameJ f j)
    connect (out0 rs) (InstPort r "1")
  when (or flat) $ do
    ra <- namedArg (f ++ "#ra")
    connect (out0 rs) (InstPort (pNode ra) "0")
  let dws = [ (slot, e, i) | (slot, WD _ e i) <- zip [1 ..] wires ]
  when (not (null dws)) $ do
    xv    <- execValue cg retTok
    owner <- Build $ gets (listToMaybe . bsActive)
    forM_ dws $ \(slot, e, i) -> do
      ctl <- spreadP xv (argvS !! (slot - 1))
      ein <- namedArg (f ++ "#e" ++ show slot)
      iin <- namedArg (f ++ "#i" ++ show slot)
      moveRet owner e ctl (InstPort (pNode ein) "0")
      moveRet owner i ctl (InstPort (pNode iin) "0")
  fst <$> resultVal f (callgroupPort cg) rsh 0

-- | A loop body must not hold streams (its tags are the loop's iterations):
-- no list literals or patterns, no reference to list-typed top-level names.
listFree :: M.Map Ident Sem.Type -> Expr -> Bool
listFree tys = go
  where
    bad x = maybe False typeHasList (M.lookup x tys)
            || x `elem` ["printl", "printlf", "printmf", "prints"]
    go = \case
      Var x         -> not (bad x)
      Lit _         -> True
      Lambda _ b    -> go b
      If c t e      -> go c && go t && go e
      Case sc alts  -> go sc && all (patOK . fst) alts && all (go . snd) alts
      Let ds b      -> all (\(FunDecl _ _ x) -> go x) ds && go b
      App a b       -> go a && go b
      BinOp _ l r   -> go l && go r
      UnOp _ x      -> go x
      List _        -> False
      Tuple es      -> all go es
      Cons _ _      -> False
      Super{}       -> True
    patOK = \case
      PCons{}   -> False
      PList _   -> False
      PTuple qs -> all patOK qs
      _         -> True

-- Literais -------------------------------------------------------------

-- | Build a constant for a 'Literal'.
litNode :: Literal -> Build Port
litNode = \case
  LInt n    -> constI n
  LFloat d  -> newNode "fconst" (NConstF "" (realToFrac d)) >>= \nid -> pure (out0 nid)
  LChar c   -> constI (fromEnum c)
  LString _ -> constI 0
  LBool b   -> constI (if b then 1 else 0)

-- Helpers --------------------------------------------------------------

-- | Convenience for a binary operation node, returning its output port.
bin2 :: String -> DNode -> Port -> Port -> Build Port
bin2 _lbl nd a b = out0 <$> bin2Node "b2" nd a b

-- | Build a binary operation node, returning its 'NodeId'.
bin2Node :: String -> DNode -> Port -> Port -> Build NodeId
bin2Node lbl nd a b = do
  ma <- getConstI a
  mb <- getConstI b
  a' <- case (ma, mb) of
          (Just k, Nothing) -> constFrom b k
          _                 -> pure a
  b' <- case (ma, mb) of
          (Nothing, Just k) -> constFrom a k
          _                 -> pure b
  ins <- alignExecInputs [a', b']
  let (a1,b1) = case ins of { [x,y] -> (x,y); _ -> (a',b') }
  nid <- newNode lbl nd
  connectPlus a1 (InstPort nid "0")
  connectPlus b1 (InstPort nid "1")
  pure nid

-- | Logical NOT implemented as equality with zero.
notP :: Port -> Build Port
notP x = do z <- constFrom x 0; bin2 "equal" (NEqual "") x z

-- | Normalize a boolean-like value to 0/1.
boolify :: Port -> Build Port
boolify x = do
  z <- constFrom x 0
  bin2 "gthan" (NGThan "") x z

-- | Logical OR implemented as @(a+b) > 0@.
orP :: Port -> Port -> Build Port
orP a b = do
  ins <- alignExecInputs [a, b]
  case ins of
    [a', b'] -> do
      s <- bin2Node "add" (NAdd "") a' b'
      z <- constFrom (out0 s) 0
      bin2 "gthan" (NGThan "") (out0 s) z
    _ -> do
      s <- bin2Node "add" (NAdd "") a b
      z <- constFrom (out0 s) 0
      bin2 "gthan" (NGThan "") (out0 s) z

-- | Logical AND using bitwise-and node.
andP :: Port -> Port -> Build Port
andP a b = do
  ins <- alignExecInputs [a, b]
  case ins of
    [a', b'] -> bin2 "band" (NBand "") a' b'
    _        -> bin2 "band" (NBand "") a b

-- | Boolean constants (1/0).
trueP, falseP :: Build Port
trueP  = constI 1
falseP = constI 0

-- CASE / Pattern matching ----------------------------------------------

-- | Compile a @case@ by building guards and steering results.
compileCase :: Expr -> [(Pattern, Expr)] -> Build Val
compileCase scr alts = do
  vscr <- goExpr scr
  case vscr of
    Scalar pscr -> case alts of
      [(p,e)] | patAlwaysTrue p -> do
        (_pp, binds) <- patPred pscr p
        withEnv $ do
          mapM_ (\(x,v) -> insertB x (BVal (Scalar v))) binds
          goExpr e
      _ -> do
        taken0 <- constFrom pscr 0
        let alts' = [ (scalarPred pscr p, e) | (p, e) <- alts ]
        steerAlts taken0 alts'
    _ -> do
      -- Streams: drop alternatives that cannot match (static count) and stop
      -- at the first one that always matches; dynamic ones test at runtime.
      let c = valRef vscr
      let classified = [ (p, e, staticMatch p (shapeOf vscr)) | (p, e) <- alts ]
          live       = cutAtYes [ a | a@(_, _, m) <- classified, m /= SMNo ]
      case live of
        [] -> Scalar <$> falseP
        ((p, e, SMYes):_) -> do
          (_, binds) <- matchVal vscr p
          withEnv $ do
            mapM_ (\(x,v) -> insertB x (BVal v)) binds
            goExpr e
        _ -> do
          taken0 <- constFrom c 0
          let alts' = [ (streamPred c vscr p, e) | (p, e, _) <- live ]
          steerAlts taken0 alts'
  where
    patAlwaysTrue = \case
      PVar{}      -> True
      PWildcard   -> True
      PTuple _    -> True
      _           -> False
    cutAtYes [] = []
    cutAtYes (a@(_, _, SMYes):_) = [a]
    cutAtYes (a:as) = a : cutAtYes as
    scalarPred pscr p = do
      (pp, bs) <- patPred pscr p
      pure (pp, [ (x, Scalar q) | (x, q) <- bs ])
    streamPred c v p = do
      (mp, bs) <- matchVal v p
      pp <- maybe (constFrom c 1) pure mp
      pure (pp, bs)
    steerAlts taken0 alts' = do
      baseK <- Build $ gets bsScopeK
      brs <- goAlts taken0 alts' [] baseK
      case brs of
        [] -> Scalar <$> falseP
        _ | joinKind (map snd brs) /= KScalar -> joinVals brs
          | otherwise -> do
              outs <- forM brs $ \(guardi, v) -> do
                val0 <- withGuard guardi (asScalar v)
                val  <- alignExecTo guardi val0
                tok  <- guardToken guardi
                sid  <- newNode "steer" (NSteer "")
                connect tok (InstPort sid "0")
                connect val (InstPort sid "1")
                pure (SteerPort sid "t")
              case outs of
                (h:rest) -> registerAlias h rest >> pure (Scalar h)
                []       -> Scalar <$> falseP
    -- Each alternative: its guard (pattern matched and no earlier one taken)
    -- and its value built under that guard.
    -- Última alternativa: NÃO compute orP/taken' (evita nó morto).
    goAlts _     []              acc _maxK = pure (reverse acc)
    goAlts taken [(mkPred,e)]    acc _maxK = do
      (_pPred, binds, guardi) <- withNoGuard $ do
        (pp0, bs) <- mkPred
        pp <- boolify pp0
        pp' <- alignExecTo taken pp
        nt  <- notP taken
        nt' <- alignExecTo pp' nt
        g   <- andP pp' nt'
        pure (pp', bs, g)
      baseK <- Build $ gets bsScopeK
      v <- withEnv $ withGuard guardi $ do
             mapM_ (\(x,w) -> insertB x (BVal w)) binds
             goExpr e
      kAfter <- Build $ gets bsScopeK
      Build $ modify (\s -> s { bsScopeK = max (max _maxK kAfter) baseK })
      pure (reverse ((guardi, v):acc))

    -- Alternativas intermediárias: mantém o cálculo de taken'
    goAlts taken ((mkPred,e):rs) acc maxK0 = do
      (_pPred, binds, guardi, taken') <- withNoGuard $ do
        (pp0, bs) <- mkPred
        pp <- boolify pp0
        pp' <- alignExecTo taken pp
        nt  <- notP taken
        nt' <- alignExecTo pp' nt
        g   <- andP pp' nt'
        tk  <- orP taken pp'
        pure (pp', bs, g, tk)
      baseK <- Build $ gets bsScopeK
      v <- withEnv $ withGuard guardi $ do
             mapM_ (\(x,w) -> insertB x (BVal w)) binds
             goExpr e
      kAfter <- Build $ gets bsScopeK
      Build $ modify (\s -> s { bsScopeK = baseK })
      goAlts taken' rs ((guardi, v):acc) (max maxK0 kAfter)

-- | Build the predicate and bindings for matching a 'Pattern' against a scrutinee port.
patPred :: Port -> Pattern -> Build (Port, [(Ident, Port)])
patPred scr = \case
  -- Tuples share the list encoding: component i = head (tail^i scr).
  PTuple ps -> do
    t <- constFrom scr 1
    let go _   []     = pure []
        go cur (q:qs) = do
          hd   <- fstDec cur
          rest <- case qs of
                    [] -> pure []
                    _  -> do tl <- sndDec cur; go tl qs
          pure ((q, hd) : rest)
    comps <- go scr ps
    subs  <- mapM (\(q, hd) -> case q of
                     PVar x    -> pure (Nothing, [(x, hd)])
                     PWildcard -> pure (Nothing, [])
                     _         -> do (pq, bq) <- patPred hd q; pure (Just pq, bq)) comps
    g <- foldM (\acc mp -> maybe (pure acc) (andP acc) mp) t (map fst subs)
    pure (g, concatMap snd subs)
  PList [] -> do
    p <- isNilP scr; pure (p, [])
  -- Treat singleton list patterns as a cons with empty tail for consistent
  -- guard construction and binding behavior.
  PList [p] -> patPred scr (PCons p (PList []))
  -- Longer list patterns: [p1, p2, ..] = p1 : [p2, ..].
  PList (p:ps) -> patPred scr (PCons p (PList ps))
  PCons ph pt -> do
    nz <- notP =<< isNilP scr
    hd <- fstDec scr
    tl <- sndDec scr
    (pH, bH) <- patPred hd ph
    (pT, bT) <- patPred tl pt
    g1 <- andP nz pH
    g2 <- andP g1 pT
    pure (g2, bH ++ bT)
  PWildcard -> do t <- constFrom scr 1; pure (t, [])
  PVar x    -> do t <- constFrom scr 1; pure (t, [(x, scr)])
  PLit lit  -> do litP <- litNodeFrom scr lit
                  eq   <- bin2 "equal" (NEqual "") scr litP
                  pure (eq, [])
  _         -> do t <- constFrom scr 1; pure (t, [])

-- | Literal helper aligned to a reference port's exec.
litNodeFrom :: Port -> Literal -> Build Port
litNodeFrom ref = \case
  LInt n    -> constFrom ref n
  LChar c   -> constFrom ref (fromEnum c)
  LBool b   -> constFrom ref (if b then 1 else 0)
  LString _ -> constFrom ref 0
  LFloat d  -> newNode "fconst" (NConstF "" (realToFrac d)) >>= \nid -> pure (out0 nid)

-- | Bind @x@ if the pattern is 'PVar'; otherwise no bindings.
bindIfVar :: Pattern -> Port -> [(Ident, Port)]
bindIfVar (PVar x) p = [(x,p)]
bindIfVar _        _ = []

-- | Literal helper that defers to 'litNode'.
litNode' :: Literal -> Build Port
litNode' = litNode
