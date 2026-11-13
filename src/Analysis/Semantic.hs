{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Semantic
Description : Semantic checks (scope, arity, duplicates) and lightweight type inference over the core AST, plus desugaring and super-name assignment utilities.
-}
module Analysis.Semantic where

import Syntax
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.State
import Control.Monad (forM, foldM, mapM_)

-- | Desugar a single declaration.
desugarDecl :: Decl -> Decl
desugarDecl (FunDecl f [] (Lambda ps e)) = FunDecl f ps e
desugarDecl d = d

-- | Desugar the entire program via 'desugarDecl'.
desugarProgram :: Program -> Program
desugarProgram (Program ds) = Program (map desugarDecl ds)

-- | Semantic (non-typing) error kinds.
data SemanticError
  = UndefinedVar Ident                 -- ^ Variable not bound in scope/signature.
  | ArityMismatch Ident Int Int        -- ^ Function name, expected arity, actual arity.
  | DuplicateFunc Ident                -- ^ Duplicated top-level function.
  | DuplicateParam Ident               -- ^ Duplicated parameter in a binder.
  | DuplicatePatternVar Ident          -- ^ Duplicated variable inside one pattern.
  deriving (Show, Eq)

-- | Type errors produced by inference.
data TypeError
  = Mismatch Expr Type Type            -- ^ Expression, expected type, actual type.
  | CondNotBool Expr Type              -- ^ Non-boolean condition in @if@.
  | BranchesTypeDiffer Expr Expr Type Type
  | BinOpTypeErr BinOperator Type Type -- ^ Ill-typed binary operator application.
  | UnOpTypeErr UnOperator Type        -- ^ Ill-typed unary operator application.
  | UnknownVar Ident                   -- ^ Variable unknown to the typing envs.
  deriving Show

-- | Unified error wrapper (semantic or typing).
data Error
  = SemErr SemanticError
  | TypErr TypeError
  deriving Show

-- | Top-level signature of functions: name ↦ arity.
type Sig = Map.Map Ident Int

-- | Variable environment for semantic checking.
type Env = Set.Set Ident

-- | Core type algebra for inference.
data Type
  = TInt | TFloat | TBool | TChar | TString
  | TList Type
  | TTuple [Type]
  | TVar String
  | TFun [Type] Type
  deriving (Eq, Show)

-- | Type schemes for let-polymorphism (forall vars . type).
data Scheme = Forall [String] Type

-- | Environment of variables and functions: name -> scheme.
type TypeEnv = Map.Map Ident Scheme

-- | Substitution of type variables.
type Subst = Map.Map String Type

-- | State: fresh-var counter plus the accumulated substitution.
data InferState = InferState { count :: Int, subst :: Subst }

-- | Inference monad: typing errors over fresh-var/substitution state.
type Infer a = ExceptT TypeError (State InferState) a

-- | Build a top-level signature (arity) from a list of declarations.
buildSig :: [Decl] -> Sig
buildSig =
  foldr
    (\(FunDecl f ps _) acc -> Map.insertWith (const id) f (length ps) acc)
    Map.empty

-- | Run semantic checks (no typing) over the program and collect all errors.
semanticCheck :: Program -> [Error]
semanticCheck prog =
  let Program ds = desugarProgram prog
      sig0 = buildSig ds
      counts = foldr (\f m -> Map.insertWith (+) f 1 m) Map.empty
               [f | FunDecl f _ _ <- ds]
      dupFs = [ SemErr (DuplicateFunc f) | (f,n) <- Map.toList counts, n > 1 ]
      errs  = concatMap (map SemErr . checkDecl sig0) ds
  in dupFs ++ errs

-- | Check a single function declaration.
-- | Built-in functions available in all scopes.
builtinFuns :: Set.Set Ident
builtinFuns = Set.fromList ["print","prints","printl","printf","printlf","printmf"]

checkDecl :: Sig -> Decl -> [SemanticError]
checkDecl sig (FunDecl _ ps b) =
  let env0 = Set.fromList ps `Set.union` builtinFuns
      dupParams = [ DuplicateParam x | x <- ps, length (filter (==x) ps) > 1 ]
  in dupParams ++ checkExpr sig env0 b

-- | Check an expression for semantic issues under a signature and env.
checkExpr :: Sig -> Env -> Expr -> [SemanticError]
checkExpr sig env expr = case expr of
  Var x
    | Set.member x env || Map.member x sig -> []
    | otherwise -> [UndefinedVar x]
  Lit _ -> []
  Lambda ps body ->
    let dups = [ p | p <- ps, length (filter (==p) ps) > 1 ]
        env' = Set.union env (Set.fromList ps)
    in map DuplicateParam dups ++ checkExpr sig env' body
  If c t e ->
    checkExpr sig env c ++ checkExpr sig env t ++ checkExpr sig env e
  Cons x xs ->
    checkExpr sig env x ++ checkExpr sig env xs
  Case scr alts ->
    checkExpr sig env scr ++ concatMap (checkAlt sig env) alts
  Let ds body ->
    let sig'     = Map.union (buildSig ds) sig
        decls    = [ (f,ps,fBody) | FunDecl f ps fBody <- ds ]
        errsDecl = concat
          [ checkExpr sig' ( Set.union env (Set.fromList (f:ps)) ) fBody
          | (f,ps,fBody) <- decls
          ]
        fnames = [ f  | (f,_,_) <- decls ]
        params = concat [ ps | (_,ps,_) <- decls ]
        env'   = Set.union env (Set.fromList (fnames ++ params))
    in errsDecl ++ checkExpr sig env' body
  App{} ->
    -- Só checamos recursivamente; NÃO emitimos mais ArityMismatch aqui.
    let (fn0,args) = flattenApp expr
        eFn = checkExpr sig env fn0
        eAs = concatMap (checkExpr sig env) args
    in eFn ++ eAs
  BinOp _ l r ->
    checkExpr sig env l ++ checkExpr sig env r
  UnOp _ x ->
    checkExpr sig env x
  List xs ->
    concatMap (checkExpr sig env) xs
  Tuple xs ->
    concatMap (checkExpr sig env) xs
  Super _ inputs _ ->
    -- First element is the function name (defined in the body), rest are input variables
    let args = drop 1 inputs
    in [UndefinedVar v | v <- args, not (Set.member v env || Map.member v sig)]

-- | Check a single case alternative (pattern + branch body).
checkAlt :: Sig -> Env -> (Pattern, Expr) -> [SemanticError]
checkAlt sig env (pat, bd) =
  let vs   = patVars pat
      dupV = [ DuplicatePatternVar v | v <- vs, length (filter (== v) vs) > 1 ]
      env' = Set.union env (Set.fromList vs)
  in dupV ++ checkExpr sig env' bd

-- | Flatten nested applications into @(function, [args])@, left to right.
flattenApp :: Expr -> (Expr, [Expr])
flattenApp (App f x) = let (fn0,xs) = flattenApp f in (fn0, xs ++ [x])
flattenApp e = (e, [])

-- | Collect variable names bound by a pattern (preorder, left-to-right).
patVars :: Pattern -> [Ident]
patVars = \case
  PWildcard -> []
  PVar x    -> [x]
  PLit _    -> []
  PList ps  -> concatMap patVars ps
  PTuple ps -> concatMap patVars ps
  PCons p ps -> patVars p ++ patVars ps

-- | Typing pass entry point: sound Hindley-Milner inference.
checkProgram :: Program -> [Error]
checkProgram prog =
  let Program ds = desugarProgram prog
      act        = inferGroup builtinEnv ds >> return ()
  in case runState (runExceptT act) (InferState 0 Map.empty) of
       (Left te, _) -> [TypErr te]
       (Right _, _) -> []

-- | Built-in functions, typed permissively (polymorphic argument, Int result).
builtinEnv :: TypeEnv
builtinEnv = Map.fromList
  [ (f, Forall ["a"] (TFun [TVar "a"] TInt))
  | f <- ["print","prints","printl","printf","printlf","printmf"] ]

freshTV :: Infer Type
freshTV = do
  s <- get
  let n = count s + 1
  put s { count = n }
  return (TVar ("t" ++ show n))

applyT :: Subst -> Type -> Type
applyT s t = case t of
  TVar a    -> Map.findWithDefault t a s
  TList e   -> TList (applyT s e)
  TTuple es -> TTuple (map (applyT s) es)
  TFun as r -> TFun (map (applyT s) as) (applyT s r)
  _         -> t

composeS :: Subst -> Subst -> Subst
composeS s1 s2 = Map.union (Map.map (applyT s1) s2) s1

ftv :: Type -> [String]
ftv t = case t of
  TVar a    -> [a]
  TList e   -> ftv e
  TTuple es -> concatMap ftv es
  TFun as r -> concatMap ftv as ++ ftv r
  _         -> []

ftvScheme :: Scheme -> [String]
ftvScheme (Forall vs t) = filter (`notElem` vs) (ftv t)

ftvEnv :: TypeEnv -> [String]
ftvEnv env = concatMap ftvScheme (Map.elems env)

extendSubst :: Subst -> Infer ()
extendSubst u = modify (\st -> st { subst = composeS u (subst st) })

unify :: Type -> Type -> Infer ()
unify a b = do
  s <- gets subst
  u <- mgu (applyT s a) (applyT s b)
  extendSubst u

mgu :: Type -> Type -> Infer Subst
mgu a b = case (a, b) of
  (TVar x, t)        -> bindVar x t
  (t, TVar x)        -> bindVar x t
  (TInt, TInt)       -> return Map.empty
  (TFloat, TFloat)   -> return Map.empty
  (TBool, TBool)     -> return Map.empty
  (TChar, TChar)     -> return Map.empty
  (TString, TString) -> return Map.empty
  (TList x, TList y) -> mgu x y
  (TTuple xs, TTuple ys)
    | length xs == length ys -> mguList xs ys
  (TFun xs rx, TFun ys ry)
    | length xs == length ys -> do
        s1 <- mguList xs ys
        s2 <- mgu (applyT s1 rx) (applyT s1 ry)
        return (composeS s2 s1)
  _ -> throwError (Mismatch (Var "<unify>") a b)

mguList :: [Type] -> [Type] -> Infer Subst
mguList [] [] = return Map.empty
mguList (x:xs) (y:ys) = do
  s1 <- mgu x y
  s2 <- mguList (map (applyT s1) xs) (map (applyT s1) ys)
  return (composeS s2 s1)
mguList _ _ = throwError (Mismatch (Var "<arity>") TInt TInt)

bindVar :: String -> Type -> Infer Subst
bindVar x t
  | t == TVar x    = return Map.empty
  | x `elem` ftv t = throwError (Mismatch (Var ("occurs " ++ x)) (TVar x) t)
  | otherwise      = return (Map.singleton x t)

instantiate :: Scheme -> Infer Type
instantiate (Forall vs t) = do
  vs' <- mapM (const freshTV) vs
  return (applyT (Map.fromList (zip vs vs')) t)

generalize :: TypeEnv -> Type -> Infer Scheme
generalize env t = do
  s <- gets subst
  let t'  = applyT s t
      evs = ftvEnv (Map.map (applySchemeS s) env)
      vs  = filter (`notElem` evs) (dedup (ftv t'))
  return (Forall vs t')
  where
    applySchemeS sb (Forall qs ty) = Forall qs (applyT (foldr Map.delete sb qs) ty)
    dedup = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

infer :: TypeEnv -> Expr -> Infer Type
infer env expr = case expr of
  Lit l  -> return (literalType l)
  Var x  -> case Map.lookup x env of
              Just sc -> instantiate sc
              Nothing -> throwError (UnknownVar x)
  Lambda ps b -> do
    tvs <- mapM (const freshTV) ps
    let env' = foldr (\(p,tv) m -> Map.insert p (Forall [] tv) m) env (zip ps tvs)
    tb <- infer env' b
    s  <- gets subst
    return (applyT s (TFun tvs tb))
  App{} -> do
    let (fn, args) = flattenApp expr
    tf  <- infer env fn
    tas <- mapM (infer env) args
    tr  <- freshTV
    unify tf (TFun tas tr)
    s   <- gets subst
    return (applyT s tr)
  If c t e -> do
    tc0 <- infer env c
    unify tc0 TBool
    tt <- infer env t
    te <- infer env e
    unify tt te
    s  <- gets subst
    return (applyT s tt)
  BinOp op l r -> do
    tl <- infer env l
    tr <- infer env r
    inferBin op tl tr
  UnOp op x -> do
    tx <- infer env x
    inferUn op tx
  Cons h t -> do
    th <- infer env h
    tt <- infer env t
    unify tt (TList th)
    s  <- gets subst
    return (applyT s (TList th))
  List xs -> do
    te <- freshTV
    mapM_ (\x -> infer env x >>= unify te) xs
    s  <- gets subst
    return (applyT s (TList te))
  Tuple xs -> do
    ts <- mapM (infer env) xs
    s  <- gets subst
    return (applyT s (TTuple ts))
  Case scr alts -> do
    tscr <- infer env scr
    tr   <- freshTV
    mapM_ (\(pat, bd) -> do
             (bs, tp) <- inferPat pat
             unify tscr tp
             let env' = foldr (\(v,t) m -> Map.insert v (Forall [] t) m) env bs
             tb <- infer env' bd
             unify tr tb) alts
    s <- gets subst
    return (applyT s tr)
  Let ds b -> do
    env' <- inferGroup env ds
    infer env' b
  Super _ _ _ -> freshTV

-- | Infer a (mutually recursive) declaration group; return env + generalized schemes.
inferGroup :: TypeEnv -> [Decl] -> Infer TypeEnv
inferGroup env ds = do
  rows <- forM ds $ \(FunDecl f ps body) -> do
    ptvs <- mapM (const freshTV) ps
    rtv  <- freshTV
    let fty = if null ps then rtv else TFun ptvs rtv
    return (f, ps, body, ptvs, rtv, fty)
  let envRec = foldr (\(f,_,_,_,_,fty) m -> Map.insert f (Forall [] fty) m) env rows
  mapM_ (\(_, ps, body, ptvs, rtv, _) -> do
           let envB = foldr (\(p,tv) m -> Map.insert p (Forall [] tv) m) envRec (zip ps ptvs)
           tb <- infer envB body
           unify tb rtv) rows
  foldM (\m (f,_,_,_,_,fty) -> do
           sc <- generalize env fty
           return (Map.insert f sc m)) env rows

inferPat :: Pattern -> Infer ([(Ident,Type)], Type)
inferPat = \case
  PWildcard  -> do tv <- freshTV; return ([], tv)
  PVar x     -> do tv <- freshTV; return ([(x,tv)], tv)
  PLit l     -> return ([], literalType l)
  PList ps   -> do
    rs <- mapM inferPat ps
    te <- freshTV
    mapM_ (unify te . snd) rs
    return (concatMap fst rs, TList te)
  PTuple ps  -> do
    rs <- mapM inferPat ps
    return (concatMap fst rs, TTuple (map snd rs))
  PCons p ps -> do
    (v1, t1) <- inferPat p
    (v2, t2) <- inferPat ps
    unify t2 (TList t1)
    return (v1 ++ v2, TList t1)

-- | Arithmetic unifies operands (matches tc on the integer core); comparisons
-- return Bool over equal operands; logical operators require Bool.
inferBin :: BinOperator -> Type -> Type -> Infer Type
inferBin op tl tr = case op of
  Add -> arith
  Sub -> arith
  Mul -> arith
  Div -> arith
  Mod -> arith
  Eq  -> comp
  Neq -> comp
  Lt  -> comp
  Le  -> comp
  Gt  -> comp
  Ge  -> comp
  And -> logic
  Or  -> logic
  where
    arith = do unify tl tr; s <- gets subst; return (applyT s tl)
    comp  = do unify tl tr; return TBool
    logic = do unify tl TBool; unify tr TBool; return TBool

inferUn :: UnOperator -> Type -> Infer Type
inferUn op tx = case op of
  Neg -> return tx
  Not -> do unify tx TBool; return TBool

literalType :: Literal -> Type
literalType = \case
  LInt _    -> TInt
  LFloat _  -> TFloat
  LBool _   -> TBool
  LChar _   -> TChar
  LString _ -> TString

-- | Full analysis: semantic (scope/arity/dup) + sound typing.
checkAll :: Program -> [Error]
checkAll p = semanticCheck p ++ checkProgram p

assignSuperNames :: Program -> Program
assignSuperNames (Program ds) =
  Program (evalState (mapM goDecl ds) superBase)
  where
    -- Reserve s0..s11 for builtin supers (list ops, prints, float mul/div).
    superBase :: Int
    superBase = 12
    goDecl (FunDecl f ps e) = FunDecl f ps <$> goExpr e
    goExpr :: Expr -> State Int Expr
    goExpr = \case
      Var x       -> pure (Var x)
      Lit l       -> pure (Lit l)
      Lambda ps b -> Lambda ps <$> goExpr b
      If c t e    -> If <$> goExpr c <*> goExpr t <*> goExpr e
      Cons h t    -> Cons <$> goExpr h <*> goExpr t
      Case s as   -> do
        s'  <- goExpr s
        as' <- mapM (\(p,e0) -> do e1 <- goExpr e0; pure (p,e1)) as
        pure (Case s' as')
      Let ds0 e0  -> do
        ds1 <- mapM (\(FunDecl f ps b) -> FunDecl f ps <$> goExpr b) ds0
        e1  <- goExpr e0
        pure (Let ds1 e1)
      App f x     -> App <$> goExpr f <*> goExpr x
      BinOp o l r -> BinOp o <$> goExpr l <*> goExpr r
      UnOp  o e0  -> UnOp  o <$> goExpr e0
      List xs     -> List  <$> mapM goExpr xs
      Tuple xs    -> Tuple <$> mapM goExpr xs
      Super _nm inputs body -> do
        i <- get
        put (i + 1)
        let nm = "s" ++ show i
        pure (Super nm inputs body)
