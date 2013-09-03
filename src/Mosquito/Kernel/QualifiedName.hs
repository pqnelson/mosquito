module Mosquito.Kernel.QualifiedName (
  Path,
  QualifiedName,
  qualifiedNamePath, qualifiedNameHead,
  mkQualifiedName, mkSimpleName,
  freshQualifiedName,
  isInfix, partialInfixKernel
)
where

  import qualified Data.List as L
  import qualified Data.Maybe as M
  import qualified Data.Set as S

  import Mosquito.Utility.Pretty

  type Path = [String]

  newtype QualifiedName = QualifiedName (Path, String)
    deriving(Eq, Show, Ord)

  qualifiedNamePath :: QualifiedName -> Path
  qualifiedNamePath (QualifiedName (path, head)) = path

  qualifiedNameHead :: QualifiedName -> String
  qualifiedNameHead (QualifiedName (path, head)) = head

  mkQualifiedName :: Path -> String -> QualifiedName
  mkQualifiedName path head = QualifiedName (path, head)

  mkSimpleName :: String -> QualifiedName
  mkSimpleName = mkQualifiedName []

  -- |Creates a freshly generated qualified name in a given path.
  freshQualifiedName :: Path         -- ^The path to put the name in
                     -> Maybe String -- ^A suggested base for the fresh name
                     -> S.Set String -- ^A set of names to avoid
                     -> QualifiedName
  freshQualifiedName path suggestion avoid =
    let base = M.fromMaybe "a" suggestion in
    let generated = generate 0 base avoid in
      mkQualifiedName path generated
    where
      generate :: Integer -> String -> S.Set String -> String
      generate counter base avoid =
        if base `S.member` avoid then
          generate 1 (base ++ show counter) avoid
        else
          base

  isInfix :: QualifiedName -> Bool
  isInfix (QualifiedName (path, head)) =
    case head of
      ['_', _, '_'] -> True
      _             -> False

  partialInfixKernel :: QualifiedName -> String
  partialInfixKernel (QualifiedName (path, ['_', k, '_'])) = [k]

  instance Pretty QualifiedName where
    pretty (QualifiedName (path, head)) =
      if null path then
        head
      else
        L.intercalate "." path ++ "." ++ head
