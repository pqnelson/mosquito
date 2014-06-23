module Mosquito.Utility.Pretty where

  class Pretty a where
    pretty :: a -> String
