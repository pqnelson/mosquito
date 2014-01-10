module Mosquito.Theories.Function (
  -- * Injectivity
  isInjectiveDecl, isInjectiveC, isInjectiveD
  -- * 
)
where

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.Theories.Boolean

  isInjectiveDecl :: Inference (Term, Theorem)
  isInjectiveDecl = do
    let name     =  mkQualifiedName ["Mosquito", "Function"] "isInjective"
    let betaType =  mkTyVar "β"
    let x        =  mkVar "x" alphaType
    let y        =  mkVar "y" alphaType
    let f        =  mkVar "f" (mkFunctionType alphaType betaType)
    fx           <- mkApp f x
    fy           <- mkApp f y
    fxfy         <- mkEquality fx fy
    xy           <- mkEquality x y
    imp          <- mkImplication fxfy xy
    ax           <- mkForall "x" alphaType imp
    bx           <- mkForall "y" alphaType ax
    let body     =  mkLam "f" (mkFunctionType alphaType betaType) bx
    primitiveNewDefinedConstant name body $ mkFunctionType (mkFunctionType alphaType betaType) boolType

  isInjectiveC :: Inference Term
  isInjectiveC = constantOfDecl isInjectiveDecl

  isInjectiveD :: Inference Theorem
  isInjectiveD = theoremOfDecl isInjectiveDecl