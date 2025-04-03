{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Arity.Types where

import Data.Text as T
import Data.Map.Strict as M
-- import Data.Set as S
import Data.List as List

import Control.Monad.State.Strict
import Data.Maybe

import Text.PrettyPrint as Pretty hiding ((<>))
import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))

type Name = T.Text
newtype Arity = Arity Int
    deriving (Eq,Ord,Show,Pretty)

instance Pretty T.Text where
    pPrint t = text . T.unpack $ t

-- Vapp/vectorized application
data Expr
    = Var Name (Maybe MType)
    | Lam [Name] Expr
    | Let   { bndr :: Name
            , rhs :: Expr
            , body :: Expr
            }
    | App Expr [Expr]
    | IntLit Int
    deriving Show

instance Pretty Expr where
    pPrint e = case e of
        Var n ty -> pPrint n <> maybe mempty (\ty -> " ::" <+> pPrint ty) ty
        Lam n e -> parens ("\\" <> (pPrint n) <> "->" <> pPrint e)
        Let bndr rhs body -> "let" <+> pPrint bndr <+> "=" <+> pPrint rhs <+> "in" <+> pPrint body
        App f args -> pPrint f <+> (pPrint args)
        IntLit n -> pPrint n

data TypeKind = Mono | Poly

data Type (k :: TypeKind) where
    -- TODO: Make arity another kind of type perhaps?
    TyVar :: Name -> MType
    FunTy :: { arityTy :: MType
             , argTys :: [MType]
             , resTy :: MType }
             -> MType
    PrimTy :: { tyCon :: Name, arityTy :: MType} -> MType -- ^ Ty Name Arity
    ArityTy :: Maybe Arity -> MType
    ForAllTy :: [Name] -> MType -> PType

mkArityTy :: Int -> MType
mkArityTy n = ArityTy $ Just $ Arity n

instance Pretty (Type k) where
    pPrint ty = case ty of
        TyVar n -> pPrint n
        FunTy arity args res -> parens
            (hcat $ List.intersperse ("->") (fmap pPrint $ args ++ [res])) <>
            pPrint arity
        PrimTy a n -> pPrint a<>pPrint n
        ForAllTy ns ty -> "forall" <+> hsep (fmap pPrint ns) <+> "." <+> pPrint ty
        ArityTy m_a ->
            let adoc = maybe "Nothing" (pPrint) m_a
            in brackets ("a:" <> adoc)

-- instance {-# OVERLAPPING #-} Pretty (Maybe Arity) where
--     pPrint Nothing = mempty
--     pPrint (Just a) = parens ("a:" <> pPrint a)

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

instance MonadFail InferM where
    fail = error

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

freshPolys :: [a] -> InferM [(Name,MType)]
freshPolys args = do
    mapM (\_ -> fresh) args

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

withVars :: [(Name,PType)] -> InferM a -> InferM a
withVars pairs act = do
    e <- getEnv
    withEnv (Prelude.foldl' (\e (k,v) -> M.insert k v e) e pairs) act

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
        FunTy arity args r -> FunTy (subst s arity) (fmap (subst s) args) (subst s r)
        PrimTy{} -> ty
        ForAllTy ns ty ->
            let s' = Prelude.foldl' (flip M.delete) s ns
            in ForAllTy ns (subst s' ty)
        ArityTy _arity -> ty -- Always either nothing or a concrete value



instance Substitutable InferState where
    subst s state = state { env = subst s (env state)}

instance Substitutable Env where
    subst s x = M.map (subst s) x


