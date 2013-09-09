-- |A module implementing qualified names of the form @Mosquito.Bool.true@
--  and similar used for identifying constants, types, lemmas, and related
--  notions throughout the Mosquito code base.
module Mosquito.Kernel.QualifiedName (
  -- * Qualified names and components
  Path,
  QualifiedName,
  -- * Utility functions and tests
  qualifiedNamePath, qualifiedNameHead,
  mkQualifiedName, mkSimpleName,
  -- * Fresh name generations
  freshQualifiedName,
  -- * Utilities for pretty printing
  isInfix, partialInfixKernel
)
where

  import qualified Data.List as L
  import qualified Data.Maybe as M
  import qualified Data.Set as S

  import Mosquito.Utility.Pretty

  -- |The type of paths (i.e. the `.' separated list of identifiers preceeding
  --  the ultimate dot in a qualified name).  Can possibly be empty for top-level
  --  unqualified names like @true@.
  type Path = [String]

  -- |The type of qualified names, consisting of a possibly empty path followed
  --  by a mandatory identifier (the `head'.)
  newtype QualifiedName = QualifiedName (Path, String)
    deriving(Eq, Show, Ord)

  -- |Returns the path of a qualified name.
  qualifiedNamePath :: QualifiedName -> Path
  qualifiedNamePath (QualifiedName (path, head)) = path

  -- |Returns the head of a qualified name.
  qualifiedNameHead :: QualifiedName -> String
  qualifiedNameHead (QualifiedName (path, head)) = head

  -- |Creates a new qualified name from a path and head.
  --  XXX: shouldn't this fail if the head is the empty string,
  --  or should those checks be elsewhere, e.g. in the parser?
  mkQualifiedName :: Path -> String -> QualifiedName
  mkQualifiedName path head = QualifiedName (path, head)

  -- |Constructs a `simple name', that is a qualified name whose path is
  --  empty and consists solely of a head.
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

  -- |Tests whether a qualified name is an infix name for pretty-printing
  --  purposes.  XXX: this is a really bad test and is broken.  Fixme.
  isInfix :: QualifiedName -> Bool
  isInfix (QualifiedName (path, head)) =
    case head of
      ['_', _, '_'] -> True
      _             -> False

  -- |Recovers the infix `kernel' of a qualified name deemed to be infix.
  --  For instance, in the qualified name @Mosquito.Bool._∧_@ the kernel
  --  is @∧@.
  partialInfixKernel :: QualifiedName -> String
  partialInfixKernel (QualifiedName (path, ['_', k, '_'])) = [k]

  instance Pretty QualifiedName where
    pretty (QualifiedName (path, head)) =
      if null path then
        head
      else
        L.intercalate "." path ++ "." ++ head