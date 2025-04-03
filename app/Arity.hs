{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Arity where

import Data.Text as T
import Data.Map.Strict as M
import Data.Set as S
import Data.List as List

-- import Control.Monad.State.Strict
-- import Data.Maybe
import Text.Megaparsec (runParser, ShowErrorComponent (..))

import Text.PrettyPrint as Pretty hiding ((<>))
import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))

import Arity.Types
import Arity.Parser
import Text.Megaparsec.Error (errorBundlePretty)

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
                s <- unify mt u_ty
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
        pure (s,FunTy (mkArityTy arity) (fmap (subst s) m_tys) t')

    App e0 args -> do
        (s0,t0) <- infer e0
        (s_args,t_args) <- inferArgs s0 args
        (_,t') <- fresh
        (_,arity_tv) <- fresh
        s2 <- unify (subst s_args t0) (FunTy arity_tv t_args t')
        pure (s2 `compose_t` s_args `compose_t` s0, subst s2 t')

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

instance FreeVars (Type k) where
    free ty = case ty of
        TyVar n -> S.singleton n
        FunTy _arity args r -> S.unions $ free r : fmap free args
        PrimTy{} -> S.empty
        ForAllTy ns ty -> Prelude.foldl' (flip S.delete) (free ty) ns
        ArityTy _ -> S.empty

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
unify' (FunTy arity1 args1 r1) (FunTy arity2 args2 r2) = do
    s <- unifyList identity (arity1:args1++[r1]) (arity2:args2++[r2])
    pure s
unify' (ArityTy arity1) (ArityTy arity2)
    | arity1 == arity2 = pure identity
    | otherwise = fail $ "Failed to unify arities:" ++ render (pPrint (arity1, arity2))
unify' ty1 ty2 = error $ "Failed to unify:" ++ show ty1 ++ " " ++ show ty2

-- unifyArity :: Maybe Arity -> Maybe Arity -> InferM Subst
-- unifyArity a1 a2
--     | a1 == Nothing = a2
--     | a2 == Nothing = a1
--     | otherwise = if


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
    putStrLn $ show (pPrint expr) ++ " =>"
    let res_ty = evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
    putStrLn $ render (pPrint res_ty)
    putStrLn ""

parseInfer :: T.Text -> IO ()
parseInfer expr_t = do
    case runParser parseExpr "" expr_t of
        Left e -> print e
        Right expr -> do
            let res_ty = evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
            putStrLn $ render (pPrint res_ty)

instance ShowErrorComponent () where
    showErrorComponent _ = ""

justParse :: T.Text -> IO ()
justParse expr_t = do
    case runParser parseExpr "" expr_t of
        Left e -> putStrLn $ errorBundlePretty e
        Right expr -> do
            print expr
            putStrLn $ render $ pPrint expr

justParseP :: (Pretty a,Show a) => Parser a -> Text -> IO ()
justParseP p expr_t = do
    case runParser p "" expr_t of
        Left e -> putStrLn $ errorBundlePretty e
        Right expr -> do
            print expr
            putStrLn $ render $ pPrint expr
main :: IO ()
main = do
    -- ptype (Var "f" $ Just (FunTy [PrimTy "Int"] (PrimTy "Int")))

    -- ptype (App (Var "f" $ Just (FunTy [PrimTy "Int"] (PrimTy "Int"))) (Var "x" $ Just (PrimTy "Int")))

    -- ptype (Lam "x" (Var "x" Nothing))

    -- ptype (Lam "x" (Var "x" (Just $ PrimTy "Int")))

    -- ptype (App (Lam "x" (Var "x" (Just $ PrimTy "Int"))) (Var "something" (Just $ PrimTy "Int")) )

    -- ptype IntLit
    -- ptype (Let "id" (Lam "x" (Var "x" Nothing)) (Var "id" Nothing))
    ptype (App (Let "id" (Lam ["x"] (Var "x" Nothing)) (Var "id" Nothing)) ([IntLit 1]))

    -- ptype (App (Var "f" $ Just $ FunTy [(TyVar "x")] (TyVar "x")) (IntLit))

    -- Expected to fail:
    -- ptype (App (Lam "x" (Var "x" (Just $ PrimTy "Int"))) (Var "y" (Just $ PrimTy "I")))
    -- print ("done" :: String)
