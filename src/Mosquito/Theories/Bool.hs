{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.Theories.Bool where

  import Prelude hiding (fail, repeat)

  import Control.Monad hiding (fail)

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.DerivedRules
  import Mosquito.Parsing

  import Mosquito.ProofState.Automation
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.Stacktics
  import Mosquito.ProofState.Tactics
  import Mosquito.ProofState.Tacticals
  import Mosquito.ProofState.Unfolding

  import Mosquito.Utility.Pretty

  --
  -- * Utility functions and definitions
  --

  fst3 :: (a, b, c) -> a
  fst3 (x, _, _) = x

  snd3 :: (a, b, c) -> b
  snd3 (_, y, _) = y

  thd3 :: (a, b, c) -> c
  thd3 (_, _, z) = z

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
        unfoldTac trueD
      , try autoBase
      , autoSolve trueD
      ] conj
    qed conj

  trueIPreTac :: PreTactic
  trueIPreTac _ concl = do
    trueC <- trueC
    if concl == trueC then
      return $ Refine (\[] -> trueI) []
    else
      fail . unwords $ [
        "Conclusion passed to `trueIPreTac' not `true'."
      ]

  -- |Solves all goals of the form @true@.
  trueITac :: Tactic
  trueITac = Mosquito.ProofState.Stacktics.selectAllGoalsTac >=> apply trueIPreTac

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
    das2  <- deductAntiSymmetric das1 eqE -- ⊢ p = (p = true)
    symm  <- symmetry das2
    equalityModusPonens symm theorem

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
    let inst =  termTypeSubst "α" ty forallC
    let lam  =  mkLam name ty body
    mkApp inst lam

  -- reflexivityThm :: Inference Theorem
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
        unfoldTac forallD
      , try combineTac
      , autoBase
      , autoSolve forallD
      , reductionTac
      , abstractTac
      , try trueEqITac
      , autoBase
      ] prf
    qed prf

  --
  -- ** Logical falsity
  --

  falseDecl :: Inference (Term, Theorem)
  falseDecl = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "false"
    forallC  <- forallC
    let inst =  termTypeSubst "α" boolType forallC
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

  -- conjunctionI :: Inference Theorem
  conjunctionI = Mosquito.Utility.Pretty.putStrLn $ do
    let p = mkVar "p" boolType
    let q = mkVar "q" boolType
    let f = mkVar "f" binaryConnectiveType
    preApp <- mkApp f p
    app    <- mkApp preApp q
    let left = mkLam "f" binaryConnectiveType app
    trueC <- trueC
    preApp' <- mkApp f trueC
    app' <- mkApp preApp' trueC
    let right = mkLam "f" binaryConnectiveType app'
    eq <- mkEquality left right
    conjunctionD <- conjunctionD
    (_, conjDef) <- fromEquality . conclusion $ conjunctionD
    eqmp'        <- mkApp conjDef p
    eqmp         <- mkApp eqmp' q
    conj         <- mkConjunction p q
    prf   <- conjecture "conjunctionI" conj
    prf   <-
      by [
        unfoldTac conjunctionD
      , try . repeat $ combineTac >=> autoBase
      , try . autoSolve $ conjunctionD
      , equalityModusPonensTac eq
      , selectGoalTac 1
      , abstractTac
      , repeat $ combineTac >=> trueEqITac
      , try autoBase
      , selectGoalTac 0
      {-
        selectGoalTac 0 >=> unfoldTac conjunctionD
      , selectGoalTac 0 >=> combineTac
      , selectAllGoalsTac >=> try alphaTac
      , selectGoalTac 0 >=> symmetryTac
      , selectGoalTac 0 >=> solveTac conjunctionD
      , selectGoalTac 0 >=> reductionTac
      , selectGoalTac 0 >=> equalityModusPonensTac eq
      , selectGoalTac 1 >=> abstractTac
      , selectGoalTac 1 >=> combineTac
      , selectGoalTac 2 >=> trueEqITac
      , selectGoalTac 1 >=> combineTac
      , selectGoalTac 2 >=> trueEqITac
      , selectGoalTac 1 >=> alphaTac
      , selectGoalTac 0 >=> symmetryTac
      , selectGoalTac 0 >=> betasTac
      -}
      ] prf
    return prf

  --
  -- ** Implication
  --

  implicationDecl :: Inference (Term, Theorem)
  implicationDecl = do
    let name    =  mkQualifiedName ["Mosquito", "Bool"] "_⇒_"
    let p       =  mkVar "p" boolType
    let q       =  mkVar "q" boolType
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