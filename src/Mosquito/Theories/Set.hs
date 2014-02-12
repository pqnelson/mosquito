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
    return $ mkLam "a" setType trueC

  setTypeExistsT = P.putStrLn $ do
    charSet <- setCharacteristicFunction
    existsD <- existsD
    trueD   <- trueD
    let s   =  mkVar "s" setType
    body    <- mkApp charSet s
    conj    <- mkExists "s" setType body
    prf     <- mkConjecture "setTypeExistsT" conj
    prf     <- act prf . Apply $ unfoldConstantP existsD
    -- XXX: bug in constant unfolding
    return prf