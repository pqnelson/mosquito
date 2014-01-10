module Mosquito.Theories.Utility (
  -- * Useful types
  binaryConnectiveType, quantifierType,
  -- * Combinators on declarations
  constantOfDecl, theoremOfDecl
)
where

  import Control.Monad hiding (fail, (>=>))

  import Mosquito.Kernel.Term

  binaryConnectiveType :: Type
  binaryConnectiveType =
    mkFunctionType boolType (mkFunctionType boolType boolType)

  quantifierType :: Type
  quantifierType = mkFunctionType (mkFunctionType alphaType boolType) boolType

  constantOfDecl :: Inference (Term, a) -> Inference Term
  constantOfDecl = liftM fst

  theoremOfDecl :: Inference (a, Theorem) -> Inference Theorem
  theoremOfDecl = liftM snd