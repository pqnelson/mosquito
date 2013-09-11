module Mosquito.Parsing where

  import qualified Data.List as L
  import qualified Data.Set as S

  import Debug.Trace (trace)

  import Text.ParserCombinators.Parsec hiding (runParser)

  import qualified Mosquito.Kernel.Term as K
  import qualified Mosquito.Utility.Pretty as P

  --
  -- ** Qualified names
  --

  type TheoryName = String

  data InfixNamePart
    = Hole
    | Piece String
      deriving (Eq, Show, Ord)

  instance P.Pretty InfixNamePart where
    pretty Hole      = "_"
    pretty (Piece p) = p

  data Head
    = Mixfix [InfixNamePart]
    | Nonfix String
    deriving (Eq, Show, Ord)

  instance P.Pretty Head where
    pretty (Nonfix n) = n
    pretty (Mixfix p) = foldr (++) "" . map P.pretty $ p

  data QualifiedName
    = QualifiedName TheoryName Head
    deriving Show

  instance P.Pretty QualifiedName where
    pretty (QualifiedName theory head) =
      L.intercalate "." [
        "Mosquito"
      , theory
      , P.pretty head
      ]

  parseTheoryName :: Parser TheoryName
  parseTheoryName = do
    x  <- many1 upper
    xs <- many  lower
    return $ x ++ xs

  parseInfixNamePart :: Parser InfixNamePart
  parseInfixNamePart =
    (string "_" >> return Hole) <|>
      do
        string <- many1 letter
        return . Piece $ string

  isValidHead :: [InfixNamePart] -> Bool
  isValidHead []                  = False
  isValidHead [Hole]              = False
  isValidHead [Piece{}]           = True
  isValidHead [Piece{}, Hole]     = True
  isValidHead [Hole, Piece{}]     = True
  isValidHead (Hole:Piece{}:xs)   = isValidHead xs
  isValidHead (Piece{}:Hole:xs)   = isValidHead xs
  isValidHead _                   = False

  parseMixfixHead :: Parser Head
  parseMixfixHead = do
    mixfix <- many1 parseInfixNamePart
    if isValidHead mixfix then
      return . Mixfix $ mixfix
    else
      fail "parseMixfixHead"

  parseNonfix :: Parser Head
  parseNonfix = do
    nonfix <- many1 $ noneOf "_"
    return . Nonfix $ nonfix

  parseHead :: Parser Head
  parseHead =
    parseNonfix <|>
    parseMixfixHead

  parseQualifiedName :: String -> Parser QualifiedName
  parseQualifiedName currentTheoryName = do
      theory <- parseTheoryName
      string "."
      head   <- parseHead
      return $ QualifiedName theory head
    <|> do
      head <- parseHead
      return $ QualifiedName currentTheoryName head

  --
  -- ** Types
  --

  parseGreekLowercaseCharacter :: Parser Char
  parseGreekLowercaseCharacter =
    oneOf "αβγδεζηθικλμνξοπρςστυφχψω" <?> "a Greek lowercase character"

  parsePrime :: Parser Char
  parsePrime = char '⎖' <?> "a prime symbol"

  parseTypeVariable :: Parser K.Type
  parseTypeVariable = (do
    greeks <- many1 parseGreekLowercaseCharacter
    primes <- many  parsePrime
    return . K.mkTyVar $ greeks ++ primes) <?> "a type variable"

  parseNonfixTypeOperator :: (String, K.TypeOperatorDescription) -> S.Set (Head, K.TypeOperatorDescription) -> Parser K.Type
  parseNonfixTypeOperator (name, description) others = do
    let arity =  K.typeOperatorDescriptionArity description
    spaces >> string name >> spaces
    args      <- count arity $ spaces >> parseFactor others
    case K.mkTyOperator description args of
      K.Fail err  -> fail ""
      K.Success d -> return d

  parseMixfix :: Parser a -> [InfixNamePart] -> Parser [a]
  parseMixfix p []        = fail ""
  parseMixfix p (Hole:xs) = do
    x  <- p
    spaces
    xs <- parseMixfix p xs
    return $ x : xs
  parseMixfix p ((Piece q):xs) = do
    spaces >> string q >> spaces
    return []

  parseMixfixTypeOperator :: ([InfixNamePart], K.TypeOperatorDescription) -> S.Set (Head, K.TypeOperatorDescription) -> Parser K.Type
  parseMixfixTypeOperator (path, description) others = do
    args <- parseMixfix (parseFactor others) path
    case K.mkTyOperator description args of
      K.Fail err  -> fail ""
      K.Success t -> return t

  parseSingletonTypeOperator :: (String, K.TypeOperatorDescription) -> Parser K.Type
  parseSingletonTypeOperator (name, description) = do
    let arity = K.typeOperatorDescriptionArity description
    if arity == 0 then do
      spaces >> string name >> spaces
      case K.mkTyOperator description [] of
        K.Fail err  -> fail ""
        K.Success t -> return t
    else
      fail ""

  parseFactor :: S.Set (Head, K.TypeOperatorDescription) -> Parser K.Type
  parseFactor config =
      parseTypeVariable <|>
      folded <|>
      between (string "(") (string ")") (parseType config)
    where
      folded = foldr (<|>) (fail "")
        $ map (\(head, descr) ->
            case head of
              Nonfix n ->
                parseSingletonTypeOperator (n, descr)
              Mixfix{} ->
                parseSingletonTypeOperator (P.pretty head, descr)) $ S.toList config

  parseType :: S.Set (Head, K.TypeOperatorDescription) -> Parser K.Type
  parseType config =
      folded <|>
      parseFactor config
    where
      folded = foldr (<|>) (fail "")
        . map (\(head, descr) ->
            case head of
              Nonfix n ->
                parseNonfixTypeOperator (n, descr) config
              Mixfix m ->
                parseNonfixTypeOperator (P.pretty head, descr) config) $ S.toList config

  kernelTypeParsingInfo :: S.Set (Head, K.TypeOperatorDescription)
  kernelTypeParsingInfo =
    S.fromList [
      (Nonfix "Bool", K.boolDescription)
    , (Mixfix [Hole, Piece "→", Hole], K.functionDescription)
    ]

  --
  -- ** Terms
  --

  data PType
    = PTyVar      String
    | PTyOperator K.TypeOperatorDescription [PType]

  instance P.Pretty PType where
    pretty (PTyVar v)            = v
    pretty (PTyOperator op args) =
      unwords [
        P.pretty op
      , unwords . map P.pretty $ args
      ]

  instance P.Size PType where
    size PTyVar{}              = 1
    size (PTyOperator op args) = 1 + (sum . map P.size $ args)

  data PTerm
    = PVar     String
    | PConst   K.ConstantDescription
    | PApp     PTerm  PTerm
    | PLam     String (Maybe PType) PTerm
    | PAscribe PTerm PType

  instance P.Size PTerm where
    size PVar{} = 1
    size PConst{} = 1
    size (PApp l r) = 1 + P.size l + P.size r
    size (PLam _ Nothing body) = 1 + P.size body
    size (PLam _ (Just ty) body) = 1 + P.size ty + P.size body
    size (PAscribe t ty) = 1 + P.size t + P.size ty

  instance P.Pretty PTerm where
    pretty (PVar v)   = v
    pretty (PConst c) = P.pretty c
    pretty (PApp l r) =
      unwords [
        P.bracket l
      , P.bracket r
      ]
    pretty (PLam nm Nothing body) =
      "λ" ++ nm ++ ". " ++ P.pretty body
    pretty (PLam nm (Just ty) body) =
      "λ(" ++ nm ++ " : " ++ P.pretty ty ++ ". " ++ P.pretty body
    pretty (PAscribe t ty) =
      "(" ++ P.pretty t ++ " : " ++ P.pretty ty ++ ")"

  --
  -- ** Running a parser
  --

  runParser :: Parser a -> String -> K.Inference a
  runParser parser input =
    case Text.ParserCombinators.Parsec.parse parser "Parsing.hs" input of
      Left err -> K.Fail . show $ err
      Right s  -> K.Success s