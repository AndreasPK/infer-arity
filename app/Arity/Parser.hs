{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Arity.Parser where

import Data.Text as T
-- import Data.Map.Strict as M
-- import Data.Set as S
import Data.List as List

-- import Control.Monad.State.Strict
-- import Data.Maybe

-- import Text.PrettyPrint as Pretty hiding ((<>))
-- import Text.PrettyPrint.HughesPJClass as Pretty hiding ((<>))

import Text.Megaparsec as P
import Text.Megaparsec.Char.Lexer as P (decimal)
import Text.Megaparsec.Char as PC

-- import Control.Monad.Combinators as PC

import Arity.Types
import Data.Char
import Data.Foldable as Foldable

type Parser a = Parsec () Text a

char_ :: Char -> Parser ()
char_ x = char x >> pure ()

parseList :: Parser a -> Parser [a]
parseList p = label "list" $ do
    char '[' >> PC.space
    (try $ do
        x <- p
        let elemP = char_ ',' >> space >> p
        xs <- manyTill (elemP) (char_ ']')
        space
        return $ x:xs)

        <|> pure []

parseList1 :: Parser a -> Parser [a]
parseList1 p = label "list" $ do
    char '[' >> PC.space
    x <- p
    let elemP = char_ ',' >> space >> p
    xs <- manyTill (elemP) (char_ ']')
    space
    return $ x:xs

parseParens :: Parser a -> Parser a
parseParens p = do
    char_ '(' >> space
    r <- p
    char_ ')' >> space
    pure r

keywords :: [Text]
keywords = ["let", "app"]

parseName :: Parser Name
parseName = label "name" $ do
    n <- (PC.letterChar :: Parser Char)
    ame <- many alphaNumChar
    space
    let name = T.pack $ n:ame
    if Prelude.elem name keywords
        then fail "Keywords parsed as name"
        else pure ()
    pure $ name

parseNames :: Parser [Name]
parseNames = parseList parseName

parseForAll :: Parser PType
parseForAll = label "forall" $ do
    string "forall" >> space
    ns <- manyTill parseName (char_ '.')
    space
    (ForAllTy ns) <$> parseMType

parseMTypeSig :: Parser MType
parseMTypeSig = string "::" >> space >> parseMType

parsePTypeSig :: Parser PType
parsePTypeSig = string "::" >> space >> parseForAll

parseMType :: Parser MType
parseMType = label "mtype" $ do
    head_ty <- try (parseParens parseMType) <|> parseTyAtom :: Parser MType
    arrow_tys <- try arrows <|> pure [] :: Parser [MType]
    let arity_ty = mkArityTy (Prelude.length arrow_tys)
    pure $ if Foldable.null arrow_tys
        then head_ty
        else FunTy arity_ty (head_ty:(List.init arrow_tys)) (List.last arrow_tys)

arrows :: Parser [MType]
arrows = do
    string "->" >> space
    ty <- try (parseParens parseMType) <|> parseTyAtom
    tys <- (try arrows) <|> pure []
    pure $ ty:tys

parseTyAtom :: Parser MType
parseTyAtom = label "tyAtom" $ do
    n <- letterChar
    ame <- many alphaNumChar
    space
    arity <- try (char_ ':' >> decimal) <|> pure 0
    space
    let name = T.pack (n:ame)
    if Data.Char.isUpper n
        then pure $ PrimTy name (mkArityTy arity)
        else pure $ TyVar name

-- parseForAll :: Parser PType

parseExpr :: Parser Expr
parseExpr =
    try (parseParens parseExpr) <|>
    try (parseInt) <|>
    try parseLam <|>
    try parseLet <|>
    try parseApp <|>
    try parseVar

parseVar, parseLam, parseLet, parseApp, parseInt :: Parser Expr
parseVar = label "var" $ do
    name <- parseName
    space
    ty <- optional parseMTypeSig
    return $ Var name ty

parseInt = label "intLiteral" $ PC.space >> IntLit <$> (decimal :: Parser Int)

parseLam = label "lambda" $ do
    char_ '\\' >> space
    vars <- ((:[]) <$> try parseName) <|> parseNames
    string "->" >> space
    body <- parseExpr
    pure $ Lam vars body

parseLet = label "let" $ do
    string "let" >> space
    bndr <- parseName
    char_ '=' >> space
    rhs <- parseExpr
    string "in" >> space
    body <- parseExpr
    pure $ Let bndr rhs body

parseApp = try parseAppE <|> parseAppV

parseAppE, parseAppV :: Parser Expr
parseAppE = label "application-exact" $ do
    string "!app" >> space
    f <- parseExpr
    args <- parseList parseExpr
    return $ AppExact f args

parseAppV = label "application" $ do
    string "app" >> space
    f <- parseExpr
    args <- parseList parseExpr
    return $ AppVague f args


