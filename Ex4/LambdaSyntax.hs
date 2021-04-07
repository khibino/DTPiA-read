module Ex4.LambdaSyntax (
  Ty (..), ty,
  Expr (..), expr, topExpr,
  ) where

import Ex4.Parser (Parser, runParser, token, eof, satisfy, char, string, perrorM)
import Control.Applicative ((<|>), many, some, optional)
import Text.Read (readEither)

{-
Type Term

data-structure
  τ := ı | τ ⇒ τ

syntax
  uτ := ı | ( cτ )
  cτ := uτ | uτ ⇒ cτ
  τ := cτ
 -}

--  "ı ⇒ ı"
--  "(ı ⇒ ı) ⇒ ı"
--  "ı ⇒ ı ⇒ ı"


data Ty
  = I
  | Ty :=>: Ty
  deriving Show

ty :: Parser Ty
ty = compoundType

unaryType :: Parser Ty
unaryType =
  tchar 'ı' *> pure I                   <|>
  tchar '(' *> compoundType <* tchar ')'

compoundType :: Parser Ty
compoundType = do
  u <- unaryType
  maybe u (u :=>:) <$> optional (tchar '⇒' *> compoundType)

_parseTy =
  mapM_
  (print . runParser (ty <* eof))
  [ "ı ⇒ ı"
  , "(ı ⇒ ı) ⇒ ı"
  , "ı ⇒ ı ⇒ ı"
  ]

---

{-
Expr Term

Data-Structure
  Expr := var Nat | Expr $ Expr | lam τ Expr

Syntax
  uE := var Nat | ( cE )
  cE := uE | uE $ cE | lam τ cE
 -}

data Expr
  = Var Integer
  | Expr :$: Expr
  | Lam Ty Expr
  deriving Show

topExpr :: Parser Expr
topExpr = expr <* eof

expr :: Parser Expr
expr = compoundExpr <* many space

unaryExpr :: Parser Expr
unaryExpr =
  tstring "var" *> pure Var <*> nat       <|>
  tchar '(' *> compoundExpr <* tchar ')'

compoundExpr :: Parser Expr
compoundExpr =
  (do u <- unaryExpr
      maybe u (u :$:) <$> optional (tchar '$' *> compoundExpr))
  <|>
  tstring "lam" *> pure Lam <*> unaryType <*> compoundExpr

_parseExpr =
  mapM_
  (print . runParser (expr <* eof))
  [ "lam (ı ⇒ ı) var 0"
  , "lam ((ı ⇒ ı) ⇒ ı) var 0"
  , "lam (ı ⇒ ı) lam ((ı ⇒ ı) ⇒ ı) var 0 $ var 1"
  , "lam ı lam (ı ⇒ ı) lam (ı ⇒ ı) var 0 $ var 1 $ var 2"
  ]

---

space :: Parser Char
space = satisfy (`elem` ['\t', '\r', '\n', ' '])

trim :: Parser a -> Parser a
trim p = many space *> p <* many space

tchar :: Char -> Parser Char
tchar = trim . char

tstring :: String -> Parser String
tstring = trim . string

digit :: Parser Char
digit = satisfy (`elem` ['0'..'9'])

nat :: Parser Integer
nat = do
  ds <- some digit <|> do { c <- token; perrorM $ "nat: some decimal digits required: found: " ++ show c }
  either (perrorM . ("nat: " ++)) pure $ readEither ds
