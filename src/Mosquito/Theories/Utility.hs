module Mosquito.Theories.Utility (
  -- * Useful types
  betaType, gammaType, deltaType,
  binaryConnectiveType, quantifierType,
  -- * Combinators on declarations
  constantOfDecl, theoremOfDecl
)
where

  import Control.Monad hiding (fail, (>=>))

  import Mosquito.Kernel.Term

  -- Alpha type is in the kernel to define equality's type

  betaType :: Type
  betaType = mkTyVar "β"

  gammaType :: Type
  gammaType = mkTyVar "γ"

  deltaType :: Type
  deltaType = mkTyVar "δ"

  binaryConnectiveType :: Type
  binaryConnectiveType =
    mkFunctionType boolType (mkFunctionType boolType boolType)

  quantifierType :: Type
  quantifierType = mkFunctionType (mkFunctionType alphaType boolType) boolType

  constantOfDecl :: Inference (Term, a) -> Inference Term
  constantOfDecl = liftM fst

  theoremOfDecl :: Inference (a, Theorem) -> Inference Theorem
  theoremOfDecl = liftM snd