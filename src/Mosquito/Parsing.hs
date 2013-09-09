module Parsing where

  import qualified Mosquito.Kernel.Term as K

  import Text.ParserCombinators.Parsec

  parseGreekCharacter :: Parser Char
  parseGreekCharacter =
    oneOf "αβγδε" <?> "a Greek character"

  parsePrime :: Parser Char
  parsePrime = char '⎖' <?> "a prime symbol"

  parseTypeVariable :: Parser K.Type
  parseTypeVariable = do
    greeks <- many1 parseGreekCharacter
    primes <- many  parsePrime
    return . K.mkTyVar $ greeks ++ primes

  data NameComponent
    = Missing
    | Piece String

  type Name = [NameComponent]

  parseNameComponent :: Parser a -> NameComponent -> Parser [a]
  parseNameComponent missing Missing   = do
    m <- missing
    return . return $ m
  parseNameComponent missing (Piece p) = do
    spaces >> string p >> spaces
    return []

  parseName :: Parser a -> Name -> Parser [a]
  parseName missing name = do
    names <- mapM (parseNameComponent missing) name
    return . concat $ names

  parseTypeOperator :: Name -> K.TypeOperatorDescription -> Parser K.Type
  parseTypeOperator name descr = do
    types <- parseName parseBracketedType name
    case K.mkTyOperator descr types of
      K.Success t -> return t
      K.Fail err  -> fail err

  parseBracketedType :: Parser K.Type
  parseBracketedType = do
    char '(' >> spaces
    phi <- parseType
    char ')' >> spaces
    return phi

  parseType :: Parser K.Type
  parseType =
    parseTypeVariable <|>
    try (parseTypeOperator [Piece "Bool"] K.boolDescription) <|>
    try (parseTypeOperator [Missing, Piece "→", Missing] K.functionDescription) <|>
    try (parseTypeOperator [Piece "if", Missing, Piece "then", Missing, Piece "else", Missing] undefined) <|>
    parseBracketedType

  parse :: Parser a -> String -> K.Inference a
  parse parser input =
    case Text.ParserCombinators.Parsec.parse parser "Parsing.hs" input of
      Left err -> K.Fail . show $ err
      Right s  -> K.Success s