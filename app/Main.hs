{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Arity where

import Data.Text as T
import Data.Map.Strict as M
import Data.Set as S
import Data.List as List

-- import Control.Monad.State.Strict
-- import Data.Maybe
import Text.Megaparsec (runParser, ShowErrorComponent (..))
import Text.Megaparsec.Error (errorBundlePretty)

import Text.PrettyPrint as Pretty hiding ((<>))
import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))

import Arity.Types
import Arity.Parser
import Arity.Inference
import Control.Monad
import Control.DeepSeq

ptype :: Expr -> IO ()
ptype expr = do
    putStrLn $ show (pPrint expr) ++ " =>"
    let res_ty = evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
    putStrLn $ render (pPrint res_ty)
    putStrLn ""

parseInfer :: Text -> IO ()
parseInfer = parseInfer' True

parseInfer' :: Bool -> T.Text -> IO ()
parseInfer' with_ast expr_t = do
    case runParser parseExpr "" expr_t of
        Left e -> putStrLn $ errorBundlePretty e
        Right expr -> do
            let res_ty = evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
            deepseq res_ty $ do
                when with_ast $ putStrLn $ "TyAst:\n\t" ++ show res_ty
                putStrLn $ "ResTy:\n\t" ++ render (pPrint res_ty)

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

parseInferDemo :: T.Text -> IO ()
parseInferDemo expr = do
    putStrLn $ T.unpack ("Expr:\n\t" <> expr)
    parseInfer' False expr
    putStrLn $ Prelude.replicate 80 '-'

foo :: (Int -> (Int -> t)) -> Int -> t
foo = \f x -> (f x) (x::Int)
main :: IO ()
main = do
    -- forever $ do
    --     putStr "Expr:"
    --     s <- getLine
    --     parseInferDemo $ T.pack s

    mapM_ parseInferDemo $
        [   -- "\\[x] -> x"
        -- ,   "\\[f,x] -> app f [x]"
        -- ,   "\\[f,x] -> !app f [x]"
        -- ,   "\\[f,g,x] -> app g [app f [x]]"
        -- ,   "\\[f,g,x] -> !app g [!app f [x]]"
        -- ,   "\\[f,g,x,y] -> app (app f [x]) [y]"
        -- ,   "\\[f,g,x] -> !app (app g [x]) [x]"

        -- forall v2 v3 . ((Int[arity:0]~>v2)[arity:1]~>Int[arity:0]~>v3)[arity:2]
        -- expected:
           "\\[f,x] -> !app (!app f [x::Int]) [x]"
        -- ,   "let apply2slow = \\[z,f,x,y] -> app f [x,y] in apply2slow"
        -- ,   "let apply2fast = \\[z,f,x,y] -> app f [x,y] in apply2slow"
        ]


        -- "let app2 = \\[f,x,y] -> app f [x,y] in app2"
    -- parseInfer "\\[f, x] -> app f [x]"
    -- parseInfer "\\[f, x] -> !app f [x]"
    -- ptype (AppExact (Let "id" (Lam ["x"] (Var "x" Nothing)) (Var "id" Nothing)) ([IntLit 1]))

