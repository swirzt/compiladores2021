-- |
-- Module      : Parse
-- Description : Define un parser de términos FD40 a términos fully named.
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Common
--( GenLanguageDef(..), emptyDef )

import Control.Monad.Identity (Identity)
import Data.Char (isNumber, ord)
import Lang
import System.IO --Para printear en test
import Text.Parsec hiding (parse, runP)
import Text.Parsec.Expr (Assoc, Operator)
import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language
import Prelude hiding (const)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------

-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer =
  Tok.makeTokenParser $
    emptyDef
      { commentLine = "#",
        reservedNames =
          [ "let",
            "fun",
            "fix",
            "then",
            "else",
            "in",
            "ifz",
            "print",
            "Nat",
            "rec",
            "type"
          ],
        reservedOpNames = ["->", ":", "=", "+", "-"]
      }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do
  pos <- getPosition
  return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom =
  (reserved "Nat" >> return SNatTy)
    <|> try (SVarTy <$> var) -- Es necesario var?
    <|> parens typeP

typeP :: P STy
typeP =
  try
    ( do
        x <- tyatom
        reservedOp "->"
        y <- typeP
        return (SFunTy x y)
    )
    <|> tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

printEta :: P STerm
printEta = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  return (SPrintEta i str)

printParse :: P STerm
printParse = try printOp <|> printEta

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table =
  [ [ binary "+" Add Ex.AssocLeft,
      binary "-" Sub Ex.AssocLeft
    ]
  ]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =
  (flip SConst <$> const <*> getPos)
    <|> flip SV <$> var <*> getPos
    <|> parens expr
    <|> printParse

multivar :: P [Name]
multivar = (do
  v <- var
  vs <- multivar
  return (v : vs))
  <|> return []

-- parsea un par (variable : tipo)
binding :: P ([Name], STy)
binding = do
  v <- multivar
  reservedOp ":"
  ty <- typeP
  return (v, ty)

singleBinding :: P (Name, STy)
singleBinding = do
  v <- var
  reservedOp ":"
  ty <- typeP
  return (v, ty)

binders :: P [([Name], STy)]
binders =
  ( do
      x <- parens binding
      xs <- binders
      return (x : xs)
  )
    <|> return []

--Si no anda, sacar el x <. parens binding arafue

lam :: P STerm
lam = do
  i <- getPos
  reserved "fun"
  xs <- binders
  reservedOp "->"
  t <- expr
  return (SLam i xs t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do
  i <- getPos
  f <- atom
  args <- many atom
  return (foldl (SApp i) f args)

fix :: P STerm
fix = do
  i <- getPos
  reserved "fix"
  (f, fty) <- parens singleBinding
  xs <- binders
  reservedOp "->"
  t <- expr
  return (SFix i f fty xs t)

ifz :: P STerm
ifz = do
  i <- getPos
  reserved "ifz"
  c <- expr
  reserved "then"
  t <- expr
  reserved "else"
  e <- expr
  return (SIfZ i c t e)

parseDef :: P (Name, [([Name], STy)], STy)
parseDef = do
  v <- var
  mvars <- binders
  reservedOp ":"
  ty <- typeP
  return (v, mvars, ty)

letexp' :: Pos -> Bool -> P STerm
letexp' i b = do
  (v, mvars, ty) <- try (parens parseDef) <|> parseDef
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i v mvars ty def body b)

letexp :: P STerm
letexp =
  do
    i <- getPos
    try
      ( do
          reserved "let"
          reserved "rec"
          letexp' i True
      )
    <|> do
      i <- getPos
      reserved "let"
      letexp' i False

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printParse <|> fix <|> letexp

decl :: P (SDecl STerm)
decl = do
  i <- getPos
  (try $ typeDecl i) <|> letdecl i

typeDecl :: Pos -> P (SDecl STerm)
typeDecl i = do
  reserved "type"
  v <- var
  reservedOp "="
  ty <- typeP
  return $ SDeclType i v ty

letdecl' :: Pos -> Bool -> P (SDecl STerm)
letdecl' i b = do
  (v, mvars, ty) <- try (parens parseDef) <|> parseDef
  reservedOp "="
  def <- expr
  return (SDeclFun i v mvars ty def b)

letdecl :: Pos -> P (SDecl STerm)
letdecl i =
  do
    reserved "let"
    try
      ( do
          reserved "rec"
          letdecl' i True
      )
      <|> letdecl' i False

-- | Parser de programas (listas de declaraciones)
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm = try (Right <$> expr) <|> (Left <$> decl)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
  Right t -> t
  Left e -> error ("no parse: " ++ show s)
