{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.Theories.Bool where

  import Prelude hiding (fail)

  import Control.Monad hiding (fail)

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.Parsing
  import Mosquito.ProofState
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
  binaryConnectiveType =
    let Success t = runParser (parseType kernelTypeParsingInfo) "_→_ Bool (_→_ Bool Bool)" in
      t

  quantifierType :: Type
  quantifierType = mkFunctionType (mkFunctionType alphaType boolType) boolType

  constantOfDecl :: Inference (Term, a) -> Inference Term
  constantOfDecl = liftM fst

  theoremOfDecl :: Inference (a, Theorem) -> Inference Theorem
  theoremOfDecl = liftM snd

  --
  -- * Logic!
  --

  --
  -- ** Logical truth
  --

  trueDecl :: Inference (Term, Theorem)
  trueDecl = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "true"
    let t    =  mkLam "a" boolType $ mkVar "a" boolType
    eq       <- mkEquality t t
    primitiveNewDefinedConstant name eq boolType

  trueC :: Inference Term
  trueC = constantOfDecl trueDecl

  trueD :: Inference Theorem
  trueD = theoremOfDecl trueDecl

  -- |Produces a derivation of @{} ⊢ true@.
  trueI :: Inference Theorem
  trueI = do
    let a =  mkVar "a" boolType
    let t =  mkLam "a" boolType a
    eq    <- mkEquality t t
    trueC <- trueC
    trueD <- trueD
    conj  <- conjecture "true-intro" trueC
    conj  <-
      by [
        equalityModusPonensTac eq
      , alphaTac
      , select 0 symmetryTac
      , select 0 $ solveTac trueD
      ] conj
    qed conj

  trueIPreTac :: PreTactic
  trueIPreTac assms concl = do
    trueC <- trueC
    if concl == trueC then
      return $ Refine (\[] -> trueI) []
    else
      fail . unwords $ [
        "Conclusion passed to `trueITac' not `true'."
      ]

  -- |Solves all goals of the form @true@.
  trueITac :: Tactic
  trueITac = 
    selectPTac (\assms concl ->
      case trueC of
        Fail{} -> False
        Success c -> concl == c) `preceeding` apply trueIPreTac

  -- |Produces a derivation of @Gamma ⊢ p@ from a derivation of
  --  @Gamma ⊢ p = true@.
  trueEqE :: Theorem -> Inference Theorem
  trueEqE theorem = do
    trueI <- trueI
    symm  <- symmetry theorem
    equalityModusPonens symm trueI

  trueEqEPreTac :: PreTactic
  trueEqEPreTac assms concl = do
    trueC <- trueC
    eq <- mkEquality concl trueC
    return $ Refine (\[t] -> trueEqE t) [Open assms eq]

  trueEqETac :: Tactic
  trueEqETac = apply trueEqEPreTac

{-

  -- |Produces a derivation of @Gamma ⊢ p = true@ from a derivation
  --  of @Gamma ⊢ p@.
  trueEqI :: Theorem -> Inference Theorem
  trueEqI theorem = do
    let p =  conclusion theorem
    assmP <- assume p  -- p ⊢ p
    trueI <- trueI     -- {} ⊢ true
    das1  <- deductAntiSymmetric assmP trueI -- p ⊢ p = true
    let c =  conclusion das1
    assmC <- assume c -- p = true ⊢ p = true
    eqE   <- trueEqE assmC -- p = true ⊢ p
    deductAntiSymmetric das1 eqE

  trueEqIPreTac :: PreTactic
  trueEqIPreTac assms concl = do
    trueC <- trueC
    (left, right) <- fromEquality concl
    if right == trueC then do
      return $ Refine (\[t] -> trueEqI t) [Open assms left]
    else
      fail "`trueEqITac'"

  trueEqITac :: Tactic
  trueEqITac = apply trueEqIPreTac

  --
  -- ** Universal quantification
  --

  forallDecl :: Inference (Term, Theorem)
  forallDecl = do
    let name  =  mkQualifiedName ["Mosquito", "Bool"] "∀"
    trueC     <- trueC
    let right =  mkLam "a" alphaType trueC
    let left  =  mkVar "P" (mkFunctionType alphaType boolType)
    eq        <- mkEquality left right
    let def   =  mkLam "P" (mkFunctionType alphaType boolType) eq
    primitiveNewDefinedConstant name def quantifierType

  forallC :: Inference Term
  forallC = constantOfDecl forallDecl

  forallD :: Inference Theorem
  forallD = theoremOfDecl forallDecl

  mkForall :: String -> Type -> Term -> Inference Term
  mkForall name ty body = do
    forallC  <- forallC
    let inst =  termTypeSubst (mkSubstitution "α" ty) forallC
    let lam  =  mkLam name ty body
    mkApp inst lam

{-
  reflexivityThm = Mosquito.Utility.Pretty.putStrLn $ do
    let t   =  mkVar "t" alphaType
    eq      <- mkEquality t t
    refl    <- reflexivity t
    trueEqI <- trueEqI refl
    conj    <- mkForall "t" alphaType eq
    forallD <- forallD
    prf     <- conjecture "reflexivity-strong" conj
    prf     <-
      by [
        selectITac (== 0) `preceeding` unfoldAppLTac forallD
      , selectITac (== 0) `preceeding` symmetryTac
      , selectITac (== 0) `preceeding` combineTac
      , selectITac (== 1) `preceeding` baseAuto
      , selectITac (== 0) `preceeding` solveTac forallD
      , selectITac (== 0) `preceeding` reductionTac
      , selectITac (== 1) `preceeding` abstractTac
      , selectITac (== 0) `preceeding` symmetryTac
      , selectITac (== 0) `preceeding` betaTac
      , selectITac (== 0) `preceeding` trueEqITac
      , selectITac (== 0) `preceeding` baseAuto
      ] prf
    qed prf
-}
  --
  -- ** Logical falsity
  --

  falseDecl :: Inference (Term, Theorem)
  falseDecl = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "false"
    forallC  <- forallC
    let inst =  termTypeSubst (mkSubstitution "α" boolType) forallC
    let body =  mkLam "a" boolType (mkVar "a" boolType)
    def      <- mkApp inst body
    primitiveNewDefinedConstant name def boolType

  falseC :: Inference Term
  falseC = constantOfDecl falseDecl

  falseD :: Inference Theorem
  falseD = theoremOfDecl falseDecl

  --
  -- ** Conjunction
  --
  conjunctionDecl :: Inference (Term, Theorem)
  conjunctionDecl = do
    let name  =  mkQualifiedName ["Mosquito", "Bool"] "_∧_"
    let f     =  mkVar "f" binaryConnectiveType
    trueC     <- trueC
    rightB    <- mkApp f trueC
    rightB    <- mkApp rightB trueC
    let right =  mkLam "f" binaryConnectiveType rightB
    leftB     <- mkApp f (mkVar "p" boolType)
    leftB     <- mkApp leftB (mkVar "q" boolType)
    let left  =  mkLam "f" binaryConnectiveType leftB
    eq        <- mkEquality left right
    let def   =  mkLam "p" boolType (mkLam "q" boolType eq)
    primitiveNewDefinedConstant name def binaryConnectiveType

  conjunctionC :: Inference Term
  conjunctionC = constantOfDecl conjunctionDecl

  conjunctionD :: Inference Theorem
  conjunctionD = theoremOfDecl conjunctionDecl

  mkConjunction :: Term -> Term -> Inference Term
  mkConjunction left right = do
    conjunctionC <- conjunctionC
    pre          <- mkApp conjunctionC left
    mkApp pre right

  --
  -- ** Implication
  --

  implicationDecl :: Inference (Term, Theorem)
  implicationDecl = do
    let name    = mkQualifiedName ["Mosquito", "Bool"] "_⇒_"
    let p       = mkVar "p" boolType
    let q       = mkVar "q" boolType
    conjunction <- mkConjunction p q
    eq          <- mkEquality conjunction p
    let def     =  mkLam "p" boolType . mkLam "q" boolType $ eq
    primitiveNewDefinedConstant name def binaryConnectiveType

  implicationC :: Inference Term
  implicationC = constantOfDecl implicationDecl

  implicationD :: Inference Theorem
  implicationD = theoremOfDecl implicationDecl

  mkImplication :: Term -> Term -> Inference Term
  mkImplication left right = do
    implicationC <- implicationC
    pre          <- mkApp implicationC left
    mkApp pre right

  --
  -- ** Negation
  --

  negationDecl :: Inference (Term, Theorem)
  negationDecl = do
    let name    =  mkQualifiedName ["Mosquito", "Bool"] "¬"
    let a       =  mkVar "a" boolType
    falseC      <- falseC
    implication <- mkImplication a falseC
    let def     =  mkLam "a" boolType implication
    primitiveNewDefinedConstant name def $ mkFunctionType boolType boolType

  negationC :: Inference Term
  negationC = constantOfDecl negationDecl

  negationD :: Inference Theorem
  negationD = theoremOfDecl negationDecl

  mkNegation :: Term -> Inference Term
  mkNegation body = do
    negationC <- negationC
    mkApp negationC body

  --
  -- ** Disjunction
  --

  disjunctionDecl :: Inference (Term, Theorem)
  disjunctionDecl = do
    let name = mkQualifiedName ["Mosquito", "Bool"] "_∨_"
    let p    = mkVar "p" boolType
    let q    = mkVar "q" boolType
    let r    = mkVar "r" boolType
    pImpR    <- mkImplication p r
    qImpR    <- mkImplication q r
    left     <- mkImplication qImpR r
    body     <- mkImplication pImpR left
    forall   <- mkForall "r" boolType body
    let def  =  mkLam "p" boolType . mkLam "q" boolType $ forall
    primitiveNewDefinedConstant name def binaryConnectiveType

  disjunctionC :: Inference Term
  disjunctionC = constantOfDecl disjunctionDecl

  disjunctionD :: Inference Theorem
  disjunctionD = theoremOfDecl disjunctionDecl

  mkDisjunction :: Term -> Term -> Inference Term
  mkDisjunction left right = do
    disjunctionC <- disjunctionC
    pre          <- mkApp disjunctionC left
    mkApp pre right
-}