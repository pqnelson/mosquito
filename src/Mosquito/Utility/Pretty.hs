{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- |A utility module used for pretty-printing values throughout the Mosquito
--  code base.
module Mosquito.Utility.Pretty (
  -- * Size metrics and pretty printing
  Size(..),
  sizes,
  Pretty(..),
  -- * Utility functions
  bracket, lift,
  -- * Pretty-printed I/O
  putStr, putStrLn
)
where

  import Prelude hiding (putStr, putStrLn)
  import qualified Prelude (putStr, putStrLn)
  import qualified Data.Foldable as F
  import qualified Data.List as L

  -- |A typeclass capturing the notion of values that can be given a
  --  size for pretty-printing purposes.  The `size' of a value should
  --  bear some relationship to the actual size of the string
  --  representation of that value under pretty-printing, for best
  --  results.
  class Size a where
    size   :: a -> Int

  -- |Sums the sizes of a series of metricisable values stored in a
  --  Foldable container.
  sizes :: (F.Foldable f, Functor f, Size a) => f a -> Int
  sizes = F.sum . fmap size

  -- |A typeclass capturing the notion of values that can be
  --  pretty-printed.  This is distinct from the Haskell Prelude
  --  Show typeclass, which is reserved for producing a faithful
  --  parsable (by GHCi) representation of a value.
  class Pretty a where
    pretty :: a -> String

  -- |Brackets a pretty-printed value with parentheses if its
  --  size, as calculated via the @Size@ typeclass, is over a given
  --  threshold, otherwise returns the unmolested output of the
  --  @pretty@ function.
  bracket :: (Pretty a, Size a) => a -> String
  bracket i
    | size i > 1 = "(" ++ pretty i ++ ")"
    | otherwise  = pretty i

  --
  -- * Useful instances
  --

  instance Pretty String where
    pretty = id

  instance Pretty a => Pretty [a] where
    pretty [] = "[]"
    pretty xs = "[" ++ (L.intercalate ", " $ map pretty xs) ++ "]"

  instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty (l, r) = "(" ++ pretty l ++ ", " ++ pretty r ++ ")"

  instance (Pretty a, Pretty b) => Pretty (Either a b) where
    pretty (Left  l) = pretty l
    pretty (Right r) = pretty r

  instance Pretty Int where
    pretty = show

  instance Pretty () where
    pretty = show

  instance Pretty Bool where
    pretty = show

  --
  -- * Input and output
  --

  -- |Lifts a function taking a @String@ to an arbitrary output
  --  to a function working over pretty-printable input.
  lift :: Pretty a => (String -> b) -> a -> b
  lift = flip (.) pretty

  -- |Version of @putStrLn@ which first transforms its input into a
  --  pretty-printed representation with @pretty@ before performing
  --  the IO action.
  putStrLn :: Pretty a => a -> IO ()
  putStrLn = lift Prelude.putStrLn

  -- |Version of @putStr@ which first transforms its input into a
  --  pretty-printed representation with @pretty@ before performing
  --  the IO action.
  putStr :: Pretty a => a -> IO ()
  putStr = lift Prelude.putStr