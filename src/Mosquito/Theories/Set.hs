module Mosquito.Theories.Set (
)
where

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.ProofState.Tactics
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.ProofState

  import Mosquito.Theories.Boolean
  import Mosquito.Theories.Utility

  import qualified Mosquito.Utility.Pretty as P

  setType :: Type
  setType = mkFunctionType alphaType boolType

  setCharacteristicFunction :: Inference Term
  setCharacteristicFunction = do
    trueC <- trueC
    return $ mkLam "x" setType trueC

  setDefiningTheorem = P.putStrLn $ do
    charSet <- setCharacteristicFunction
    existsD <- existsD
    trueD   <- trueD
    let s   =  mkVar "s" setType
    body    <- mkApp charSet s
    conj    <- mkExists "s" setType body
    prf     <- mkConjecture "setDefiningTheorem" conj
    prf     <- act prf . Apply $ unfoldConstantPreTactic existsD
    return prf