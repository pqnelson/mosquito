module Mosquito.Theories.Function (
  -- * Simple combinators
  idDecl, idC, idD,
  constDecl, constC, constD,
  applyDecl, applyC, applyD, mkApply,
  flipDecl, flipC, flipD,
  composeDecl, composeC, composeD, mkCompose,
  -- * Properties of functions
  isInjectiveDecl, isInjectiveC, isInjectiveD,
  isSurjectiveDecl, isSurjectiveC, isSurjectiveD,
  isBijectiveDecl, isBijectiveC, isBijectiveD
)
where

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.Theories.Boolean
  import Mosquito.Theories.Utility

  --
  -- * Simple combinators
  --

  idDecl :: Inference (Term, Theorem)
  idDecl = do
    let name = mkQualifiedName ["Mosquito", "Function"] "id"
    let x    = mkVar "x" alphaType
    let body = mkLam "x" alphaType x
    primitiveNewDefinedConstant name body $ mkFunctionType alphaType alphaType

  idC :: Inference Term
  idC = constantOfDecl idDecl

  idD :: Inference Theorem
  idD = theoremOfDecl idDecl

  constDecl :: Inference (Term, Theorem)
  constDecl = do
    let name = mkQualifiedName ["Mosquito", "Function"] "const"
    let x    = mkVar "x" alphaType
    let y    = mkVar "y" betaType
    let body = mkLam "x" alphaType (mkLam "y" betaType x)
    primitiveNewDefinedConstant name body $ mkFunctionType alphaType (mkFunctionType betaType alphaType)

  constC :: Inference Term
  constC = constantOfDecl constDecl

  constD :: Inference Theorem
  constD = theoremOfDecl constDecl

  applyDecl :: Inference (Term, Theorem)
  applyDecl = do
    let name =  mkQualifiedName ["Mosquito", "Function"] "_$_"
    let x    =  mkVar "x" alphaType
    let fty  =  mkFunctionType alphaType betaType
    let f    =  mkVar "f" fty
    fx       <- mkApp f x
    let body =  mkLam "f" fty $ mkLam "x" alphaType fx
    primitiveNewDefinedConstant name body $ mkFunctionType fty (mkFunctionType alphaType betaType)

  applyC :: Inference Term
  applyC = constantOfDecl applyDecl

  applyD :: Inference Theorem
  applyD = theoremOfDecl applyDecl

  mkApply :: Term -> Term -> Inference Term
  mkApply f x = do
    applyC <- applyC
    fapply <- mkApp applyC f
    mkApp fapply x

  flipDecl :: Inference (Term, Theorem)
  flipDecl = do
    let name =  mkQualifiedName ["Mosquito", "Function"] "flip"
    let fty  =  mkFunctionType alphaType $ mkFunctionType betaType gammaType
    let f    =  mkVar "f" fty
    let x    =  mkVar "x" alphaType
    let y    =  mkVar "y" betaType
    fx       <- mkApp f x
    fxy      <- mkApp fx y
    let body =  mkLam "f" fty $ mkLam "y" betaType $ mkLam "x" alphaType fxy
    primitiveNewDefinedConstant name body $ mkFunctionType fty $ mkFunctionType betaType $ mkFunctionType alphaType gammaType

  flipC :: Inference Term
  flipC = constantOfDecl flipDecl

  flipD :: Inference Theorem
  flipD = theoremOfDecl flipDecl

  composeDecl :: Inference (Term, Theorem)
  composeDecl = do
    let name =  mkQualifiedName ["Mosquito", "Function"] "_◦_"
    let fty  =  mkFunctionType betaType gammaType
    let gty  =  mkFunctionType alphaType betaType
    let f    =  mkVar "f" fty
    let g    =  mkVar "g" gty
    let x    =  mkVar "x" alphaType
    gx       <- mkApp g x
    fgx      <- mkApp f gx
    let body =  mkLam "f" fty $ mkLam "g" gty $ mkLam "x" alphaType fgx
    primitiveNewDefinedConstant name body $ mkFunctionType fty $ mkFunctionType gty $ mkFunctionType alphaType gammaType

  composeC :: Inference Term
  composeC = constantOfDecl composeDecl

  composeD :: Inference Theorem
  composeD = theoremOfDecl composeDecl

  mkCompose :: Term -> Term -> Inference Term
  mkCompose f g = do
    composeC <- composeC
    fc       <- mkApp composeC f
    mkApp fc g

  --
  -- * Properties of functions
  --

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

  isSurjectiveDecl :: Inference (Term, Theorem)
  isSurjectiveDecl = do
    let name = mkQualifiedName ["Mosquito", "Function"] "isSurjective"
    let fty  = mkFunctionType alphaType betaType
    let f    = mkVar "f" fty
    let x    = mkVar "x" alphaType
    let y    = mkVar "y" betaType
    fx       <- mkApp f x
    fxy      <- mkEquality fx y
    exfxy    <- mkExists "x" alphaType fxy
    ayexfxy  <- mkForall "y" betaType exfxy
    let body =  mkLam "f" fty ayexfxy
    primitiveNewDefinedConstant name body $ mkFunctionType fty boolType

  isSurjectiveC :: Inference Term
  isSurjectiveC = constantOfDecl isSurjectiveDecl

  isSurjectiveD :: Inference Theorem
  isSurjectiveD = theoremOfDecl isSurjectiveDecl

  isBijectiveDecl :: Inference (Term, Theorem)
  isBijectiveDecl = do
    let name =  mkQualifiedName ["Mosquito", "Function"] "isBijective"
    let fty  =  mkFunctionType alphaType betaType
    let f    =  mkVar "f" fty
    surjC    <- isSurjectiveC
    injC     <- isInjectiveC
    fs       <- mkApp surjC f
    fi       <- mkApp injC f
    conj     <- mkConjunction fs fi
    let body =  mkLam "f" fty conj
    primitiveNewDefinedConstant name body $ mkFunctionType fty boolType

  isBijectiveC :: Inference Term
  isBijectiveC = constantOfDecl isBijectiveDecl

  isBijectiveD :: Inference Theorem
  isBijectiveD = theoremOfDecl isBijectiveDecl