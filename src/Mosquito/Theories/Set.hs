module Mosquito.Theories.Set (
)
where

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.ProofState.Tactics
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.Unfolding

  import Mosquito.Theories.Boolean
  import Mosquito.Theories.Utility

  import Mosquito.Utility.Pretty

  setType :: Type
  setType = mkFunctionType alphaType boolType

  setCharacteristicFunction :: Inference Term
  setCharacteristicFunction = do
    trueC <- trueC
    return $ mkLam "x" setType trueC

  setDefiningTheorem = do
    charSet <- setCharacteristicFunction
    existsD <- existsD
    let s   =  mkVar "s" setType
    body    <- mkApp charSet s
    conj    <- mkExists "s" setType body
    prf     <- mkConjecture "setDefiningTheorem" conj
    prf     <- act prf $ unfoldTactic existsD
    return prf