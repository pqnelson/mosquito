{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Mosquito.Theories.Theory
where

  import Data.Label
  import qualified Data.Map as M

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  data Theory
    = Theory {
      _theorems  :: M.Map QualifiedName Theorem
    }

  mkLabels [''Theory]

  basis :: Theory
  basis = Theory { _theorems = M.empty }
