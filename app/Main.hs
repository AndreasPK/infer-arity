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
import Text.Megaparsec.Error (errorBundlePretty)

import Text.PrettyPrint as Pretty hiding ((<>))
import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))

import Arity.Types
import Arity.Parser
import Arity.Inference

ptype :: Expr -> IO ()
ptype expr = do
    putStrLn $ show (pPrint expr) ++ " =>"
    let res_ty = evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
    putStrLn $ render (pPrint res_ty)
    putStrLn ""

parseInfer :: T.Text -> IO ()
parseInfer expr_t = do
    case runParser parseExpr "" expr_t of
        Left e -> putStrLn $ errorBundlePretty e
        Right expr -> do
            let res_ty = evalInfer $ (snd <$> infer expr) >>= \t -> abstract t
            print res_ty
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
    justParse $
        "let app2 = \\[z,f,x,y] -> app f [x,y] in app app2 [x :: Int]"
    parseInfer $
        "let app2 = \\[z,f,x,y] -> app f [x,y] in app app2 [x :: Int]"
        -- "let app2 = \\[f,x,y] -> app f [x,y] in app2"
    -- parseInfer "\\[f, x] -> app f [x]"
    -- parseInfer "\\[f, x] -> !app f [x]"
    -- ptype (AppExact (Let "id" (Lam ["x"] (Var "x" Nothing)) (Var "id" Nothing)) ([IntLit 1]))

