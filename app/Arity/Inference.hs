{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Arity.Inference where

-- import Data.Text as T
import Data.Map.Strict as M
import Data.Set as S
import Data.List as List

-- import Control.Monad.State.Strict
-- import Data.Maybe

import Text.PrettyPrint as Pretty hiding ((<>))
import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))

import Arity.Types
import qualified Data.Text as T
import qualified Data.List as L
import Debug.Trace
import qualified Data.Foldable as F

traceMDebug :: Monad m => String -> m ()
traceMDebug = traceM
-- traceMDebug _ = pure ()

infer :: Expr -> InferM (Subst, MType)
infer expr = case expr of
    IntLit _n ->
        pure (identity, PrimTy "Int" (mkArityTy 0))
    Var n (Just u_ty) -> do
        pt <- lookMaybe n
        case pt of
            Nothing -> pure (identity, u_ty)
            Just pt' -> do
                mt <- instantiate pt'
                s <- mustUnify $ unify mt u_ty
                pure (s, subst s mt)

    Var n Nothing -> do
        pt <- look n
        mt <- instantiate pt
        pure (identity, mt)

    Lam ns body -> do
        let arity = List.length ns

        m_tys <- fmap snd <$> freshPolys ns
        (s,t') <- withVars
                    (Prelude.zip ns (List.map (ForAllTy []) m_tys)) $
                    infer body
        let arg_tys = fmap (subst s) m_tys
            res_ty = FunTy (mkFunArityKind arity) arg_tys t'

        -- traceMDebug $ ('\n':) $  render $ hang "Lam" 6 $ (
        --     "bndr_tys:" <> pPrint m_tys $$
        --     "s:" <> prettyMapping s $$
        --     "arg_tys:" <> pPrint arg_tys $$
        --     "body_ty:" <> pPrint t' $$
        --     "lam:" <> pPrint res_ty $$
        --     "_Lam")
        pure (s,res_ty)

    AppExact e0 args -> do
        (f0,t0) <- infer e0
        (s_args,t_args) <- inferArgs f0 args
        -- v0 => Int -> v2

        (_,t') <- fresh
        s2 <- mustUnify $
                unify   (subst s_args t0)
                        (FunTy (mkFunArityKind $ Prelude.length args) t_args t')
        -- s2: v2 -> Int->v3

        let res_ty = subst s2 t'
            res_subst = s2 `compose_t` s_args `compose_t` f0

        -- traceMDebug $ render $ hang "AppExact" 6 (
        --     "s_f:" <> prettyMapping s_args $$
        --     "s_args:" <> prettyMapping s_args $$
        --     "t0:" <> pPrint t0 $$
        --     "s2:" <> prettyMapping s2 $$
        --     "expr:" <> pPrint expr $$
        --     "expr:" <> pPrint expr $$
        --     "res_subst" <> prettyMapping res_subst $$
        --     "res_ty::" <> pPrint res_ty
        --     )

        pure (res_subst, res_ty)

    AppVague f args -> do
        (f0,fun_ty) <- infer f
        (s_args,t_args) <- inferArgs f0 args
        (_,t') <- fresh
        -- (_,arity_tv) <- fresh

        let fun_ty' = subst s_args fun_ty

        let pap_fun_ty = case fun_ty' of
                    FunTy _kind f_arg_tys f_r_ty
                        | length f_arg_tys > length args
                        ->  let (t_app,t_un_app) = L.splitAt (L.length args) f_arg_tys
                            in FunTy CurriedFun t_app (FunTy CurriedFun t_un_app f_r_ty)
                    _ -> fun_ty'
        fun_subst <- mustUnify $ unify pap_fun_ty (FunTy CurriedFun t_args t')

        -- s2 <- unify (subst s_args t_f') (FunTy CurriedFun t_args t')
        pure (fun_subst `compose_t` s_args `compose_t` f0, subst fun_subst t')

    Let n e0 e1 -> do
        (s0,t) <- infer e0
        e <- getEnv
        let e' = subst s0 e
        pt <- withEnv e' $ abstract t
        (s1,t1) <- withEnv e' $ withVar (n,pt) $ infer e1
        pure (s1 `compose_t` s0, t1)

inferArgs :: Subst -> [Expr] -> InferM (Subst,[MType])
inferArgs s args = go s [] args
    where
        go s tys [] = pure (s,Prelude.reverse tys)
        go s tys (arg:args) = do
            (s',ty) <- withSubst s $ infer arg
            go (compose_t s s') (ty:tys) args


instantiate :: PType -> InferM MType
instantiate (ForAllTy ns ty) = do
    mtys <- mapM (\_ -> snd <$> fresh) ns
    let mty = subst (M.fromList (Prelude.zip ns mtys)) ty
    pure mty

class FreeVars a where
    free :: a -> S.Set Name

instance FreeVars FunKind where
    free fk = case fk of
        CurriedFun -> mempty
        VectoredFun n -> free n

instance FreeVars (Type k) where
    free ty = case ty of
        TyVar n -> S.singleton n
        FunTy arity args r -> S.unions $ free arity : free r : fmap free args
        PrimTy{} -> S.empty
        ForAllTy ns ty -> F.foldl' (flip S.delete) (free ty) ns
        ArityTy _ -> S.empty

abstract :: MType -> InferM PType
abstract mty =
    let ns = free mty
    in pure $ ForAllTy (S.elems ns) mty

newtype UnifyM a = UnifyM (Either T.Text a)
    deriving (Applicative, Functor, Monad)

mustUnify :: UnifyM a -> InferM a
mustUnify (UnifyM act) = do
    case act of
        Left err -> fail $ "Required unification failed:" ++ show err
        Right r -> pure r

mightUnify :: UnifyM a -> InferM (Maybe a)
mightUnify (UnifyM act) = do
    pure $ case act of
        Left _err -> Nothing
        Right r -> Just r

unifies :: Subst -> UnifyM Subst
unifies s = UnifyM $ Right s

apart :: T.Text -> UnifyM a
apart err = UnifyM $ Left err

unify :: MType -> MType -> UnifyM Subst
unify ty1 ty2 = do
    r <- unify' ty1 ty2
    return r
unify' :: MType -> MType -> UnifyM Subst
unify' ty1 ty2
    | ty1 == ty2 = unifies $ identity
unify' (TyVar n1) ty2 = doTyVar n1 ty2
unify' ty1 (TyVar n2) = doTyVar n2 ty1
unify' f1@(FunTy k1 args1 r1) f2@(FunTy k2 args2 r2) = do
    case () of
      _
        | VectoredFun a1 <- k1
        , VectoredFun a2 <- k2
        -> unifyList identity (a1:args1++[r1]) (a2:args2++[r2])
        | CurriedFun <- k1
        , CurriedFun <- k2
        -> unifyList identity (args1++[r1]) (args2++[r2])
        | otherwise -> apart $ T.pack $ "Failed to unify function arities:" ++ render (pPrint (f1,f2))
unify' (ArityTy arity1) (ArityTy arity2)
    | arity1 == arity2 = unifies identity
    | otherwise = apart $ T.pack $ "Failed to unify arities:" ++ render (pPrint (arity1, arity2))
unify' ty1 ty2 = apart $ T.pack $ "Failed to unify:" ++ show ty1 ++ " " ++ show ty2 ++ "\n" ++ (render $ pPrint (ty1,ty2))

unifyList :: Subst -> [MType] -> [MType] -> UnifyM Subst
unifyList s [] [] = unifies s
unifyList s (ty1:tys1) (ty2:tys2) = do
    s' <- unify (subst s ty1) (subst s ty2)
    unifyList (compose_t s s') tys1 tys2
unifyList _ _ _ = apart "Impossible/arg count missmatch"

doTyVar :: Name -> MType -> UnifyM Subst
doTyVar nm ty = case ty of
    TyVar nm2
        | otherwise ->  unifies $ M.singleton ((max nm nm2)) (TyVar (min nm nm2))
    _ ->                unifies $ M.singleton nm ty