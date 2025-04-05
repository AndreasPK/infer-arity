{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}

module Arity.Types where

import Data.Text as T
import Data.Map.Strict as M
-- import Data.Set as S
import Data.List as List
import Data.Foldable as F

import Control.Monad.State.Strict
import GHC.Generics
import Data.Maybe

import Text.PrettyPrint as Pretty hiding ((<>))
import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))
import Control.DeepSeq

type Name = T.Text
data Arity = KnownArity Int | TopArity
    deriving (Eq,Ord,Show)

instance NFData Arity where
    rnf a = case a of
        KnownArity a -> rnf a
        TopArity -> ()

instance Pretty Arity where
    pPrint TopArity = "*"
    pPrint (KnownArity n) = pPrint n

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

    | AppExact Expr [Expr]

    | AppVague Expr [Expr]

    | IntLit Int
    deriving (Show,Generic)

instance Pretty Expr where
    pPrint e = case e of
        Var n ty -> pPrint n <> maybe mempty (\ty -> " ::" <+> pPrint ty) ty
        Lam n e -> parens ("\\" <> (pPrint n) <> "->" <> pPrint e)
        Let bndr rhs body -> "let" <+> pPrint bndr <+> "=" <+> pPrint rhs <+> "in" <+> pPrint body
        AppExact f args -> "!app" <+> parens (pPrint f) <+> (pPrint args)
        AppVague f args -> "app" <+> parens (pPrint f) <+> (pPrint args)
        IntLit n -> pPrint n

data TypeKind = Mono | Poly deriving (Eq,Generic)

data FunKind = VectoredFun { fun_arityTy :: MType }
             -- ^ The "squiggly arrow" in some literature.
             | CurriedFun
             -- ^ Regular haskell like functions
    deriving (Eq,Show)

instance NFData FunKind where
    rnf k = case k of
        CurriedFun -> ()
        VectoredFun a -> rnf a

data Type (k :: TypeKind) where
    -- TODO: Make arity another kind of type perhaps?
    TyVar :: Name -> MType
    FunTy :: { funKind :: FunKind
             , argTys :: [MType]
             , resTy :: MType }
             -> MType
    PrimTy :: { tyCon :: Name, type_arityTy :: MType} -> MType -- ^ Ty Name Arity
    ArityTy :: Arity -> MType
    ForAllTy :: [Name] -> MType -> PType

instance NFData (Type k) where
    rnf ty = case ty of
        TyVar n -> rnf n
        FunTy a b c -> rnf (a,b,c)
        PrimTy a b -> rnf (a,b)
        ArityTy a -> rnf a
        ForAllTy a b -> rnf (a,b)


mkArityTy :: Int -> MType
mkArityTy n = ArityTy $ KnownArity n

mkFunArityKind :: Int -> FunKind
mkFunArityKind n = VectoredFun $ mkArityTy n

instance Pretty (Type k) where
    pPrint ty = case ty of
        TyVar n -> pPrint n
        FunTy f_kind args res ->
            case f_kind of
                CurriedFun -> parens (hcat $ List.intersperse ("->") (fmap pPrint $ args ++ [res]))
                VectoredFun arity ->
                    parens ((hcat $ List.intersperse ("~>") (fmap pPrint args)) <> "~>" <> pPrint res) <> brackets (pPrint arity)
        PrimTy a n -> pPrint a<>
            if n == ArityTy (KnownArity 0) then mempty
                else brackets (pPrint n)
        ForAllTy ns ty -> "forall" <+> hsep (fmap pPrint ns) <+> "." <+> pPrint ty
        ArityTy m_a ->
            let adoc = pPrint m_a
            in ("arity:" <> adoc)

-- instance {-# OVERLAPPING #-} Pretty (Maybe Arity) where
--     pPrint Nothing = mempty
--     pPrint (Just a) = parens ("a:" <> pPrint a)

deriving instance Eq (Type k)
deriving instance Show (Type k)

type MType = Type Mono
type PType = Type Poly

type Env = M.Map Name PType

prettyMapping :: (Pretty k,Pretty v) => M.Map k v -> Doc
prettyMapping m =
    brackets $ hcat $ List.intersperse "," $ fmap (\(k,v) -> pPrint k <> "=>" <> pPrint v) (M.toList m)

data InferState = InferState
    {   idx :: Int
    ,   env :: Env
    } deriving Generic

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
    withEnv (F.foldl' (\e (k,v) -> M.insert k v e) e pairs) act

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
    subst s x = fmap (subst s) x
        -- M.mapWithKey (\k v -> subst s (fromMaybe v (M.lookup k s))) x

compose :: Subst -> Subst -> Subst
compose s1 s2 = compose_t s1 s2

compose_t :: Subst -> Subst -> Subst
compose_t s2 s1 =
    let s1' = subst s2 s1
    in M.union s1' s2

instance Substitutable (FunKind) where
    subst s k = case k of
        CurriedFun -> CurriedFun
        VectoredFun arity -> VectoredFun (subst s arity)
instance Substitutable (Type k) where
    subst s ty = case ty of
        TyVar n -> fromMaybe ty (M.lookup n s)
        FunTy arity args r -> FunTy (subst s arity) (fmap (subst s) args) (subst s r)
        PrimTy{} -> ty
        ForAllTy ns ty ->
            let s' = F.foldl' (flip M.delete) s ns
            in ForAllTy ns (subst s' ty)
        ArityTy _arity -> ty -- Always either nothing or a concrete value

instance Substitutable InferState where
    subst s state = state { env = subst s (env state)}

instance Substitutable Env where
    subst s x = M.map (subst s) x


