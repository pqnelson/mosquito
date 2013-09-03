module Mosquito.Theories.Bool where

  import Control.Monad hiding (fail)

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.DerivedRules
  import Mosquito.Tactics
  import Mosquito.Theory

  import Mosquito.Utility.Pretty

  --
  -- * Utility functions and definitions
  --

  fst3 :: (a, b, c) -> a
  fst3 (x, y, z) = x

  snd3 :: (a, b, c) -> b
  snd3 (x, y, z) = y

  thd3 :: (a, b, c) -> c
  thd3 (x, y, z) = z

  binaryConnectiveType :: Type
  binaryConnectiveType = mkFunctionType boolType (mkFunctionType boolType boolType)

  quantifierType :: Type
  quantifierType = mkFunctionType (mkFunctionType alphaType boolType) boolType

  constantOfDecl :: Inference (Term, a) -> Inference Term
  constantOfDecl decl = decl >>= \decl -> return . fst $ decl

  theoremOfDecl :: Inference (a, Theorem) -> Inference Theorem
  theoremOfDecl decl = decl >>= \decl -> return . snd $ decl