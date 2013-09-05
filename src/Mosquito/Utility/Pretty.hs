{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Mosquito.Utility.Pretty (
  Size(..),
  Pretty(..),
  bracket,
  lift, putStr, putStrLn
)
where

  import Prelude hiding (putStr, putStrLn)
  import qualified Prelude (putStr, putStrLn)
  import qualified Data.List as L

  class Size a where
    size   :: a -> Int

  class Pretty a where
    pretty :: a -> String

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

  --
  -- * Input and output
  --

  lift :: Pretty a => (String -> b) -> a -> b
  lift f = f . pretty

  putStrLn :: Pretty a => a -> IO ()
  putStrLn = lift Prelude.putStrLn

  putStr :: Pretty a => a -> IO ()
  putStr = lift Prelude.putStr