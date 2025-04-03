{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Simple where

import Data.Text as T
import Data.Map.Strict as M
import Data.Set as S

import Control.Monad.State.Strict
import Data.Maybe

type Name = T.Text

data Expr
    = Var Name (Maybe MType)
    | Lam Name Expr
    | Let   { bndr :: Name
            , rhs :: Expr
            , body :: Expr
            }
    | App Expr Expr
    | IntLit
    deriving Show

data TypeKind = Mono | Poly

data Type (k :: TypeKind) where
    TyVar :: Name -> MType
    FunTy :: [MType] -> MType -> MType
    PrimTy :: Name -> MType
    ForAllTy :: [Name] -> MType -> PType

deriving instance Eq (Type k)
deriving instance Show (Type k)

type MType = Type Mono
type PType = Type Poly

type Env = M.Map Name PType

data InferState = InferState
    {   idx :: Int
    ,   env :: Env
    }

newtype InferM a = InferM (State InferState a)
    deriving (Functor, Applicative,Monad, MonadState InferState)

evalInfer :: InferM a -> (a)
evalInfer (InferM act) =
    evalState act (InferState {idx = 0, env = mempty})

incIdx :: InferM Int
incIdx = do
    s <- get
    put $ s {idx = idx s + 1}
    return $ idx s

newName :: InferM Name
newName = do
    i <- incIdx
    pure $ T.pack $ "v" ++ show i

fresh :: InferM (Name,MType)
fresh = do
    n <- newName
    pure (n,TyVar n)

look :: Name -> InferM (PType)
look n = do
    s <- get
    let ty = fromMaybe (error $ "unknown" ++ show n) $ M.lookup n (env s)
    return ty

lookMaybe :: Name -> InferM (Maybe PType)
lookMaybe n = do
    s <- get
    let ty = M.lookup n (env s)
    return ty

getEnv :: InferM Env
getEnv = env <$> get

withEnv :: Env -> InferM a -> InferM a
withEnv env_in act = do
    s <- get
    put $ s {env = env_in}
    r <- act
    s' <- get
    put $ s' {env = env s}
    pure r

withVar :: (Name,PType) -> InferM a -> InferM a
withVar (n,pty) act = do
    e <- getEnv
    withEnv (M.insert n pty e) act

withSubst :: Subst -> InferM a -> InferM a
withSubst s act = do
    e <- getEnv
    let e' = subst s e
    withEnv e' act

type Subst = M.Map Name MType

identity :: Subst
identity = M.empty

class Substitutable a where
    subst :: Subst -> a -> a

instance Substitutable Subst where
    subst s x = M.mapWithKey (\k v -> fromMaybe v (M.lookup k s)) x

compose :: Subst -> Subst -> Subst
compose s1 s2 = compose_t s1 s2

compose_t :: Subst -> Subst -> Subst
compose_t s1 s2 =
    let s1' = subst s2 s1
    in M.union s2 s1'

instance Substitutable (Type k) where
    subst s ty = case ty of
        TyVar n -> fromMaybe ty (M.lookup n s)
        FunTy args r -> FunTy (fmap (subst s) args) (subst s r)
        PrimTy{} -> ty
        ForAllTy ns ty ->
            let s' = Prelude.foldl' (flip M.delete) s ns
            in ForAllTy ns (subst s' ty)

instance Substitutable InferState where
    subst s state = state { env = subst s (env state)}

instance Substitutable Env where
    subst s x = M.map (subst s) x

infer :: Expr -> InferM (Subst, MType)
infer expr = case expr of
    IntLit ->
        pure (identity, PrimTy "Int")
    Var n (Just u_ty) -> do
        pt <- lookMaybe n
        case pt of
            Nothing -> pure (identity, u_ty)
            Just pt' -> do
                mt <- instantiate pt'
                s <- unify mt u_ty
                pure (s, subst s mt)

    Var n Nothing -> do
        pt <- look n
        mt <- instantiate pt
        pure (identity, mt)

    Lam n body -> do
        (_,t) <- fresh
        let pt = ForAllTy [] t
        (s,t') <- withVar (n,pt) $ infer body
        pure (s,FunTy [subst s t] t')

    App e0 e1 -> do
        (s0,t0) <- infer e0
        (s1,t1) <- withSubst s0 $ infer e1
        (_,t') <- fresh
        s2 <- unify (subst s1 t0) (FunTy [t1] t')
        pure (s2 `compose_t` s1 `compose_t` s0, subst s2 t')


    Let n e0 e1 -> do
        (s0,t) <- infer e0
        e <- getEnv
        let e' = subst s0 e
        pt <- withEnv e' $ abstract t
        (s1,t1) <- withEnv e' $ withVar (n,pt) $ infer e1
        pure (s1 `compose_t` s0, t1)


instantiate :: PType -> InferM MType
instantiate (ForAllTy ns ty) = do
    mtys <- mapM (\_ -> snd <$> fresh) ns
    let mty = subst (M.fromList (Prelude.zip ns mtys)) ty
    pure mty

class FreeVars a where
    free :: a -> S.Set Name

instance FreeVars (Type k) where
    free ty = case ty of
        TyVar n -> S.singleton n
        FunTy args r -> S.unions $ free r : fmap free args
        PrimTy{} -> S.empty
        ForAllTy ns ty -> Prelude.foldl' (flip S.delete) (free ty) ns

abstract :: MType -> InferM PType
abstract mty =
    let ns = free mty
    in pure $ ForAllTy (S.elems ns) mty

unify :: MType -> MType -> InferM Subst
unify ty1 ty2 = do
    r <- unify' ty1 ty2
    return r
unify' :: MType -> MType -> InferM Subst
unify' ty1 ty2
    | ty1 == ty2 = pure $ identity
unify' (TyVar n1) ty2 = doTyVar n1 ty2
unify' ty1 (TyVar n2) = doTyVar n2 ty1
unify' (FunTy args1 r1) (FunTy args2 r2) = do
    unifyList identity (args1++[r1]) (args2++[r2])
unify' ty1 ty2 = error $ "Failed to unify:" ++ show ty1 ++ " " ++ show ty2

unifyList :: Subst -> [MType] -> [MType] -> InferM Subst
unifyList s [] [] = pure s
unifyList s (ty1:tys1) (ty2:tys2) = do
    s' <- unify (subst s ty1) (subst s ty2)
    unifyList (compose_t s s') tys1 tys2
unifyList _ _ _ = error "Impossible/arg count missmatch"

doTyVar :: Name -> MType -> InferM Subst
doTyVar nm ty = case ty of
    TyVar nm2
        | otherwise -> pure $ M.singleton ((max nm nm2)) (TyVar (min nm nm2))
    _ -> pure $ M.singleton nm ty


ptype :: Expr -> IO ()
ptype expr = do
    putStrLn $ show expr ++ " =>"
    print $ evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
    putStrLn ""

main :: IO ()
main = do
    -- ptype (Var "f" $ Just (FunTy [PrimTy "Int"] (PrimTy "Int")))

    -- ptype (App (Var "f" $ Just (FunTy [PrimTy "Int"] (PrimTy "Int"))) (Var "x" $ Just (PrimTy "Int")))

    -- ptype (Lam "x" (Var "x" Nothing))

    -- ptype (Lam "x" (Var "x" (Just $ PrimTy "Int")))

    -- ptype (App (Lam "x" (Var "x" (Just $ PrimTy "Int"))) (Var "something" (Just $ PrimTy "Int")) )

    -- ptype IntLit
    -- ptype (Let "id" (Lam "x" (Var "x" Nothing)) (Var "id" Nothing))
    ptype (App (Let "id" (Lam "x" (Var "x" Nothing)) (Var "id" Nothing)) (IntLit))

    -- ptype (App (Var "f" $ Just $ FunTy [(TyVar "x")] (TyVar "x")) (IntLit))

    -- Expected to fail:
    -- ptype (App (Lam "x" (Var "x" (Just $ PrimTy "Int"))) (Var "y" (Just $ PrimTy "I")))
    -- print ("done" :: String)

