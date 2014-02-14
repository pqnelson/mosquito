{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.Theories.Boolean {- (
  -- * Utility functions and definitions
  binaryConnectiveType, quantifierType,
  constantOfDecl, theoremOfDecl,
  -- * Logic
  -- ** Logical truth
  trueDecl, trueC, trueD,
  trueI, trueILocalEdit, trueIPreTactic,
  trueEqI, trueEqILocalEdit, trueEqIPreTactic,
  trueEqE, trueEqELocalEdit, trueEqEPreTactic,
  -- ** Universal quantification
  forallDecl, forallC, forallD,
  mkForall, fromForall,
  -- ** Logical falsity
  falseDecl, falseC, falseD,
  -- ** Conjunction
  conjunctionDecl, conjunctionC, conjunctionD,
  mkConjunction, fromConjunction,
  -- ** Material implication
  implicationDecl, implicationC, implicationD,
  mkImplication, fromImplication,
  -- ** Negation
  negationDecl, negationC, negationD,
  mkNegation, fromNegation,
  -- ** Disjunction
  disjunctionDecl, disjunctionC, disjunctionD,
  mkDisjunction, fromDisjunction,
  -- ** Existential quantification
  existsDecl, existsC, existsD,
  mkExists, fromExists,
  -- ** If, and only if
  iffDecl, iffC, iffD,
  mkIff, fromIff
  -- ** Unique existence
  uniqueExistsDeclaration, uniqueExistsC, uniqueExistsD,
  mkUniqueExists, fromUniqueExists
) -} where

  import Prelude hiding (fail, repeat)

  import Debug.Trace

  import Mosquito.DerivedRules
  import Mosquito.TermUtilities

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.ProofState.Automation
  import Mosquito.ProofState.Conversionals
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics

  import Mosquito.Theories.Theory
  import Mosquito.Theories.Utility

  import Mosquito.Utility.Extlib
  import Mosquito.Utility.Pretty

  --
  -- ** Boolean theory
  --

  boolTheoryName :: QualifiedName
  boolTheoryName = mkQualifiedName ["Mosquito"] "Boolean"

  boolTheory :: Theory
  boolTheory =
    newTheory [primitiveHOL] boolTheoryName


  --
  -- ** Logical truth
  --

  trueTheory :: Inference Theory
  trueTheory = do
    let t    =  mkLam "a" boolType $ mkVar "a" boolType
    eq       <- mkEquality t t
    registerNewDefinition boolTheory "true" eq boolType

  -- |Produces a derivation of @{} ⊢ true@.
  trueIntroductionT :: Inference Theorem
  trueIntroductionT = do
    thy   <- trueTheory
    trueC <- getConstantCurrent thy "true"
    trueD <- getTheoremCurrent thy "trueD"
    conj  <- mkConjecture "trueIntroduction" trueC
    conj  <- act conj $ Apply (unfoldConstantP trueD)
    conj  <- act conj $ Apply alphaP
    qed conj

  -- |Solves goals of the form @Gamma |- true@.
  trueIntroductionL :: LocalEdit
  trueIntroductionL _ concl = do
    userMark ["trueIntroductionL:", pretty concl]
    thy   <- trueTheory
    trueC <- getConstantCurrent thy "true"
    if concl == trueC then
      return (\[] -> trueIntroductionT, [])
    else
      fail . unwords $ [
        "trueIntroductionL: conclusion `", pretty concl, "' not `true'."
      ]

  -- |Solves goals of the form @true@.
  trueIntroductionP :: PreTactic
  trueIntroductionP = mkPreTactic "trueIntroductionP" trueIntroductionL

  -- |Produces a derivation of @Gamma ⊢ p@ from a derivation of
  --  @Gamma |- p = true@.
  trueEqualityEliminationR :: Theorem -> Inference Theorem
  trueEqualityEliminationR thm = do
    trueI <- trueIntroductionT
    symm  <- symmetryR thm
    equalityModusPonensR symm trueI

  trueEqualityEliminationL :: LocalEdit
  trueEqualityEliminationL assms concl = do
    userMark ["trueEqualityEliminationL:", pretty concl]
    thy   <- trueTheory
    trueC <- getConstantCurrent thy "true"
    eq <- mkEquality concl trueC
    return (\[t] -> trueEqualityEliminationR t, [(assms, eq)])

  trueEqualityEliminationP :: PreTactic
  trueEqualityEliminationP = mkPreTactic "trueEqualityEliminationP" trueEqualityEliminationL

  -- |Produces a derivation of @Gamma ⊢ p = true@ from a derivation
  --  of @Gamma ⊢ p@.
  trueEqualityIntroductionR :: Theorem -> Inference Theorem
  trueEqualityIntroductionR thm = do
    let p =  conclusion thm
    assmP <- assumeR p  -- p ⊢ p
    trueI <- trueIntroductionT     -- {} ⊢ true
    das1  <- deductAntiSymmetricR assmP trueI -- p ⊢ p = true
    let c =  conclusion das1
    assmC <- assumeR c -- p = true ⊢ p = true
    eqE   <- trueEqualityEliminationR assmC -- p = true ⊢ p
    das2  <- deductAntiSymmetricR das1 eqE -- ⊢ p = (p = true)
    symm  <- symmetryR das2
    equalityModusPonensR symm thm

  trueEqualityIntroductionL :: LocalEdit
  trueEqualityIntroductionL assms concl = do
    userMark ["trueEqualityIntroductionL:", pretty concl]
    thy   <- trueTheory
    trueC <- getConstantCurrent thy "true"
    (left, right) <- fromEquality concl
    if right == trueC then do
      return $ (\[t] -> trueEqualityIntroductionR t, [(assms, left)])
    else
      fail "`trueEqILocalEdit'"

  trueEqualityIntroductionP :: PreTactic
  trueEqualityIntroductionP = mkPreTactic "trueEqualityIntroductionP" trueEqualityIntroductionL

  --
  -- ** Universal quantification
  --

{-
  forallDeclaration :: Inference (Term, Theorem)
  forallDeclaration = do
    let name  =  mkQualifiedName ["Mosquito", "Bool"] "∀"
    trueC     <- trueC
    let right =  mkLam "a" alphaType trueC
    let left  =  mkVar "P" (mkFunctionType alphaType boolType)
    eq        <- mkEquality left right
    let def   =  mkLam "P" (mkFunctionType alphaType boolType) eq
    primitiveNewDefinedConstant name def quantifierType

  forallC :: Inference Term
  forallC = constantOfDecl forallDeclaration

  forallD :: Inference Theorem
  forallD = theoremOfDecl forallDeclaration

  mkForall :: String -> Type -> Term -> Inference Term
  mkForall name ty body = do
    forallC  <- forallC
    let subst = mkSubstitution [("α", ty)]
    let inst =  termTypeSubst subst forallC
    let lam  =  mkLam name ty body
    mkApp inst lam

  mkForalls :: [(String, Type)] -> Term -> Inference Term
  mkForalls []           t = return t
  mkForalls ((n, ty):xs) t = do
    tail <- mkForalls xs t
    head <- mkForall n ty tail
    return head

  fromForall :: Term -> Inference (String, Type, Term)
  fromForall term = do
    (forallC, body) <- fromApp term
    fromLam body

  forallEliminationR :: Term -> Theorem -> Inference Theorem
  forallEliminationR trm thm = do
    forallC  <- forallC
    forallD  <- forallD
    let x    =  mkVar "x" alphaType
    let p    =  mkVar "P" (mkFunctionType alphaType boolType)
    allP     <- mkApp forallC p
    assmAllP <- assumeR allP
    allDP    <- combineLeftR p forallD
    eqmp     <- equalityModusPonensR allDP assmAllP
    conv     <- conversionR betaR eqmp
    conv'    <- combineLeftR x conv
    conv''   <- conversionR (combineRConv betaR) conv'
    trueE    <- trueEqualityEliminationR conv''
    return trueE

  --
  -- ** Logical falsity
  --

  falseDeclaration :: Inference (Term, Theorem)
  falseDeclaration = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "false"
    forallC  <- forallC
    let subst = mkSubstitution [("α", boolType)]
    let inst =  termTypeSubst subst forallC
    let body =  mkLam "a" boolType (mkVar "a" boolType)
    def      <- mkApp inst body
    primitiveNewDefinedConstant name def boolType

  falseC :: Inference Term
  falseC = constantOfDecl falseDeclaration

  falseD :: Inference Theorem
  falseD = theoremOfDecl falseDeclaration

  --
  -- ** Conjunction
  --

  -- |The declaration of the conjunction constant.
  conjunctionDeclaration :: Inference (Term, Theorem)
  conjunctionDeclaration = do
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

  -- |The conjunction constant.
  conjunctionC :: Inference Term
  conjunctionC = constantOfDecl conjunctionDeclaration

  -- |The conjunction defining theorem.
  conjunctionD :: Inference Theorem
  conjunctionD = theoremOfDecl conjunctionDeclaration

  -- |Makes a conjunction from two terms.
  mkConjunction :: Term -> Term -> Inference Term
  mkConjunction left right = do
    conjunctionC <- conjunctionC
    pre          <- mkApp conjunctionC left
    mkApp pre right

  -- |Destructs a conjunction.
  fromConjunction :: Term -> Inference (Term, Term)
  fromConjunction term = do
    (pre, right)  <- fromApp term
    (conjC, left) <- fromApp pre
    return (left, right)

  -- |Conjunction introduction rule.
  conjunctionIntroductionR :: Theorem -> Theorem -> Inference Theorem
  conjunctionIntroductionR left right = do
    conjD  <- conjunctionD
    let f  =  mkVar "f" binaryConnectiveType
    assmL  <- assumeR . conclusion $ left
    assmR  <- assumeR . conclusion $ right
    assmLT <- trueEqualityIntroductionR assmL
    assmRT <- trueEqualityIntroductionR assmR
    comb   <- combineRightR f assmLT
    comb'  <- combineR comb assmRT
    abs    <- abstractR "f" binaryConnectiveType comb'
    cL     <- combineLeftR (conclusion left) conjD
    cR     <- combineLeftR (conclusion right) cL
    beta   <- conversionR (replaceEverywhereConv . tryConv $ betaR) cR
    symm   <- symmetryR beta
    eqmp   <- equalityModusPonensR symm abs
    p      <- proveHypothesisR left eqmp
    q      <- proveHypothesisR right p
    return q

  -- |Conjunction introduction local edit.  Transforms goals of the form @Gamma |- P /\ Q@
  --  into goals @Gamma |- P@ and @Gamma |- Q@.
  conjunctionIntroductionL :: LocalEdit
  conjunctionIntroductionL assms concl = do
    userMark ["conjunctionIntroductionL", pretty concl]
    (left, right) <- fromConjunction concl
    return (\[left, right] -> conjunctionIntroductionR left right, [(assms, left), (assms, right)])

  -- |Conjunction introduction pretactic.
  conjunctionIntroductionP :: PreTactic
  conjunctionIntroductionP = mkPreTactic "conjunctionIntroductionP" conjunctionIntroductionL

  -- |Conjunction elimination 1 rule.
  conjunctionElimination1R :: Theorem -> Inference Theorem
  conjunctionElimination1R thm = do
    let x         =  mkVar "x" boolType
    let y         =  mkVar "y" boolType
    let term      =  mkLams [("x", boolType), ("y", boolType)] x
    (left, right) <- fromConjunction . conclusion $ thm
    conjD         <- conjunctionD
    leftC         <- combineLeftR left conjD
    leftC'        <- conversionR (combineRConv betaR) leftC
    rightC        <- combineLeftR right leftC'
    rightC'       <- conversionR (combineRConv betaR) rightC
    assm          <- assumeR . conclusion $ thm
    eqmp          <- equalityModusPonensR rightC' assm
    elim          <- combineLeftR term eqmp
    beta          <- conversionR (replaceEverywhereConv . tryConv $ betaR) elim
    beta'         <- conversionR (replaceEverywhereConv . tryConv $ betaR) beta
    trueE         <- trueEqualityEliminationR beta'
    p             <- proveHypothesisR thm trueE
    return p

  -- |Conjunction elimination 1 local edit.  Transforms goals of the form @Gamma |- P@
  --  into goals of the form @Gamma |- P /\ Q@.
  conjunctionElimination1L :: Term -> LocalEdit
  conjunctionElimination1L trm assms concl = do
    conj <- mkConjunction trm concl
    return (\[t] -> conjunctionElimination1R t, [(assms, conj)])

  -- |Conjunction elimination 1 pretactic.
  conjunctionElimination1P :: Term -> PreTactic
  conjunctionElimination1P = mkPreTactic "conjunctionElimination1P" . conjunctionElimination1L

  -- |Conjunction elimination 2 rule.
  conjunctionElimination2R :: Theorem -> Inference Theorem
  conjunctionElimination2R thm = do
    let x         =  mkVar "x" boolType
    let y         =  mkVar "y" boolType
    let term      =  mkLams [("x", boolType), ("y", boolType)] y
    (left, right) <- fromConjunction . conclusion $ thm
    conjD         <- conjunctionD
    leftC         <- combineLeftR left conjD
    leftC'        <- conversionR (combineRConv betaR) leftC
    rightC        <- combineLeftR right leftC'
    rightC'       <- conversionR (combineRConv betaR) rightC
    assm          <- assumeR . conclusion $ thm
    eqmp          <- equalityModusPonensR rightC' assm
    elim          <- combineLeftR term eqmp
    beta          <- conversionR (replaceEverywhereConv . tryConv $ betaR) elim
    beta'         <- conversionR (replaceEverywhereConv . tryConv $ betaR) beta
    trueE         <- trueEqualityEliminationR beta'
    p             <- proveHypothesisR thm trueE
    return p

  -- |Conjunction elimination 2 local edit.  Transforms goals of the form @Gamma |- Q@
  --  into goals of the form @Gamma |- P /\ Q@.
  conjunctionElimination2L :: Term -> LocalEdit
  conjunctionElimination2L trm assms concl = do
    conj <- mkConjunction concl trm
    return (\[t] -> conjunctionElimination2R t, [(assms, conj)])

  -- |Conjunction elimination 2 pretactic.
  conjunctionElimination2P :: Term -> PreTactic
  conjunctionElimination2P = mkPreTactic "conjunctionElimination2P" . conjunctionElimination2L

  --
  -- ** Implication
  --

  -- |The declaration and definition of material implication.
  implicationDeclaration :: Inference (Term, Theorem)
  implicationDeclaration = do
    let name    =  mkQualifiedName ["Mosquito", "Bool"] "_⇒_"
    let p       =  mkVar "p" boolType
    let q       =  mkVar "q" boolType
    conjunction <- mkConjunction p q
    eq          <- mkEquality conjunction p
    let def     =  mkLam "p" boolType . mkLam "q" boolType $ eq
    primitiveNewDefinedConstant name def binaryConnectiveType

  -- |The implication constant.
  implicationC :: Inference Term
  implicationC = constantOfDecl implicationDeclaration

  -- |The implication defining theorem.
  implicationD :: Inference Theorem
  implicationD = theoremOfDecl implicationDeclaration

  -- |Makes an implication from two boolean-typed terms.
  mkImplication :: Term -> Term -> Inference Term
  mkImplication left right = do
    implicationC <- implicationC
    pre          <- mkApp implicationC left
    mkApp pre right

  -- |Destructs an implication.
  fromImplication :: Term -> Inference (Term, Term)
  fromImplication term = do
    impC          <- implicationC
    (pre, right)  <- fromApp term
    (impC', left) <- fromApp pre
    if impC == impC' then
      return (left, right)
    else
      fail . unwords $ [
        "fromImplication: term `", pretty term, "' is not an implication."
      ]

  isImplication :: Term -> Bool
  isImplication trm = do
    inference (fromImplication trm)
      (const True)
      (const False)

  -- |Implication elimination (modus ponens) rule.
  implicationEliminationR :: Theorem -> Theorem -> Inference Theorem
  implicationEliminationR left right = do
    (hyp, conc) <- fromImplication . conclusion $ left
    if hyp == conclusion right then do
      imp   <- mkImplication hyp conc
      impD  <- implicationD
      impL  <- combineLeftR hyp impD
      impR  <- combineLeftR conc impL
      beta  <- conversionR (replaceEverywhereConv . tryConv $ betaR) impR
      assm  <- assumeR imp
      eqmp  <- equalityModusPonensR beta assm
      assmL <- assumeR hyp
      symm  <- symmetryR eqmp
      eqmp' <- equalityModusPonensR symm assmL
      conj  <- conjunctionElimination2R eqmp'
      p     <- proveHypothesisR left conj
      q     <- proveHypothesisR right p
      return q
    else
      fail . unwords $ [
        unwords ["implicationEliminationR: antecedent of implicational theorem `", pretty left, "' does"]
      , unwords ["not match conclusion of right hand theorem `", pretty right, "'."]
      ]

  -- |Implication elimination (modus ponens) local edit.  Transforms goals of the form
  --  @Gamma |- Q@ into goals @Gamma |- P ==> Q@ and @Gamma |- P@.
  implicationEliminationL :: Term -> LocalEdit
  implicationEliminationL trm assms concl = do
    imp <- mkImplication trm concl
    return (\[left, right] -> implicationEliminationR left right, [(assms, imp), (assms, trm)])

  -- |Implication elimination (modus ponens) pretactic.
  implicationEliminationP :: Term -> PreTactic
  implicationEliminationP = mkPreTactic "implicationEliminationP" . implicationEliminationL

  -- |Implication introduction rule.
  implicationIntroductionR :: Term -> Theorem -> Inference Theorem
  implicationIntroductionR trm thm = do
    impD <- implicationD
    impT <- combineLeftR trm impD
    impT' <- combineLeftR (conclusion thm) impT
    beta  <- conversionR (replaceEverywhereConv . tryConv $ betaR) impT'
    symm  <- symmetryR beta
    assm  <- assumeR trm
    conj  <- conjunctionIntroductionR assm thm
    assm' <- assumeR (conclusion conj)
    cnj1  <- conjunctionElimination1R assm'
    das   <- deductAntiSymmetricR conj cnj1
    eqmp  <- equalityModusPonensR symm das
    return eqmp

  -- |Implication introduction local edit.  Transforms goals of the form
  --  @Gamma |- P ==> Q@ in to goals of the form @Gamma, P |- Q@.
  implicationIntroductionL :: LocalEdit
  implicationIntroductionL assms concl = do
    userMark ["implicationIntroductionL:", pretty concl]
    (left, right) <- fromImplication concl
    return (\[t] -> implicationIntroductionR left t, [(left:assms, right)])

  -- |Implication introduction pretactic.
  implicationIntroductionP :: PreTactic
  implicationIntroductionP = mkPreTactic "implicationIntroductionP" implicationIntroductionL

  --
  -- ** Negation
  --

  -- |The declaration and definition of the negation constant.
  negationDeclaration :: Inference (Term, Theorem)
  negationDeclaration = do
    let name    =  mkQualifiedName ["Mosquito", "Bool"] "¬"
    let a       =  mkVar "a" boolType
    falseC      <- falseC
    implication <- mkImplication a falseC
    let def     =  mkLam "a" boolType implication
    primitiveNewDefinedConstant name def $ mkFunctionType boolType boolType

  -- |The negation constant.
  negationC :: Inference Term
  negationC = constantOfDecl negationDeclaration

  -- |The negation defining theorem.
  negationD :: Inference Theorem
  negationD = theoremOfDecl negationDeclaration

  -- |Makes a negation from a boolean-typed term.
  mkNegation :: Term -> Inference Term
  mkNegation body = do
    negationC <- negationC
    mkApp negationC body

  -- |Destructs a negation.
  fromNegation :: Term -> Inference Term
  fromNegation term = do
    negC <- negationC
    (negC', body) <- fromApp term
    if negC == negC' then
      return body
    else
      fail . unwords $ [
        "fromNegation: term `", pretty term, "' is not a negation."
      ]

  -- |Tests whether a term is a negation.
  isNegation :: Term -> Bool
  isNegation trm =
    inference (fromNegation trm)
      (const False)
      (const True)

  negationIntroductionR :: Theorem -> Inference Theorem
  negationIntroductionR thm = do
    negD         <- negationD
    (hyp, concl) <- fromImplication . conclusion $ thm
    concNegD     <- combineLeftR hyp negD
    conv         <- conversionR (replaceEverywhereConv . tryConv $ betaR) concNegD
    symm         <- symmetryR conv
    eqmp         <- equalityModusPonensR symm thm
    return eqmp

  negationIntroductionL :: LocalEdit
  negationIntroductionL assms concl = do
    if isNegation concl then do
      term   <- fromNegation concl
      falseC <- falseC
      imp    <- mkImplication term falseC
      return (\[t] -> negationIntroductionR t, [(assms, imp)])
    else
      fail . unwords $ [
        "negationIntroductionL: goal `", pretty concl, "' is not a negation."
      ]

  negationIntroductionP :: PreTactic
  negationIntroductionP = mkPreTactic "negationIntroductionP" negationIntroductionL

  negationEliminationR :: Theorem -> Inference Theorem
  negationEliminationR thm = do
    negationD <- negationD
    body      <- fromNegation . conclusion $ thm
    comb      <- combineLeftR body negationD
    conv      <- conversionR (replaceEverywhereConv . tryConv $ betaR) comb
    eqmp      <- equalityModusPonensR conv thm
    return eqmp

  negationEliminationL :: LocalEdit
  negationEliminationL assms concl = do
    if isImplication concl then do
      falseC      <- falseC
      (hyp, conc) <- fromImplication concl
      if falseC == conc then do
        neg <- mkNegation hyp
        return (\[t] -> negationEliminationR t, [(assms, neg)])
      else
        fail . unwords $ [
          "negationEliminationL: conclusion of goal `", pretty concl, "' is not false."
        ]
    else
      fail . unwords $ [
        "negationEliminationL: goal `", pretty concl, "' is not an implication."
      ]

  negationEliminationP :: PreTactic
  negationEliminationP = mkPreTactic "negationEliminationP" negationEliminationL

  --
  -- ** Disjunction
  --

  -- |The declaration and definition of disjunction.
  disjunctionDeclaration :: Inference (Term, Theorem)
  disjunctionDeclaration = do
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

  -- |The disjunction constant.
  disjunctionC :: Inference Term
  disjunctionC = constantOfDecl disjunctionDeclaration

  -- |The disjunction defining theorem.
  disjunctionD :: Inference Theorem
  disjunctionD = theoremOfDecl disjunctionDeclaration

  -- |Makes a disjunction from two boolean-typed terms.
  mkDisjunction :: Term -> Term -> Inference Term
  mkDisjunction left right = do
    disjunctionC <- disjunctionC
    pre          <- mkApp disjunctionC left
    mkApp pre right

  fromDisjunction :: Term -> Inference (Term, Term)
  fromDisjunction term = do
    (pre, right) <- fromApp term
    (disjC, left) <- fromApp pre
    return (left, right)

  --
  -- ** Existential quantification
  --

  -- |The declaration and definition of the existential quantifier.
  existsDeclaration :: Inference (Term, Theorem)
  existsDeclaration = do
    let name  =  mkQualifiedName ["Mosquito", "Bool"] "∃"
    let p     =  mkVar "P" $ mkFunctionType alphaType boolType
    let q     =  mkVar "q" boolType
    let x     =  mkVar "x" alphaType
    let aBool = mkFunctionType alphaType boolType
    px        <- mkApp p x
    pxq       <- mkImplication px q
    apxq      <- mkForall "x" alphaType pxq
    pqxqq     <- mkImplication apxq q
    qpqxqq    <- mkForall "q" boolType pqxqq
    let body  =  mkLam "P" aBool qpqxqq
    primitiveNewDefinedConstant name body quantifierType

  -- |The existential quantifier constant.
  existsC :: Inference Term
  existsC = constantOfDecl existsDeclaration

  -- |The existential quantifier defining theorem.
  existsD :: Inference Theorem
  existsD = theoremOfDecl existsDeclaration

  -- |Makes an existential quantification from a term and
  --  typed variable.
  mkExists :: String -> Type -> Term -> Inference Term
  mkExists name ty body = do
    existsC   <- existsC
    let subst =  mkSubstitution [("α", ty)]
    let inst  =  termTypeSubst subst existsC
    let lam   =  mkLam name ty body
    mkApp inst lam

  fromExists :: Term -> Inference (String, Type, Term)
  fromExists term = do
    (quantifier, lam) <- fromApp term
    fromLam lam

  --
  -- ** If and only if
  --

  iffDeclaration :: Inference (Term, Theorem)
  iffDeclaration = do
    let name = mkQualifiedName ["Mosquito", "Bool"] "_⇔_"
    let p    = mkVar "p" boolType
    let q    = mkVar "q" boolType
    pq       <- mkImplication p q
    qp       <- mkImplication q p
    body     <- mkConjunction pq qp
    let lp   =  mkLam "p" boolType body
    let lq   =  mkLam "q" boolType lp
    primitiveNewDefinedConstant name lq binaryConnectiveType

  iffC :: Inference Term
  iffC = constantOfDecl iffDeclaration

  iffD :: Inference Theorem
  iffD = theoremOfDecl iffDeclaration

  mkIff :: Term -> Term -> Inference Term
  mkIff left right = do
    iffC <- iffC
    left <- mkApp iffC left
    mkApp left right

  fromIff :: Term -> Inference (Term, Term)
  fromIff body = do
    (pre, right) <- fromApp body
    (iffC, left) <- fromApp pre
    return (left, right)

  --
  -- * Unique existence
  --

  -- | ex x. p /\ forall y. p y ==> x = y
  uniqueExistsDeclaration :: Inference (Term, Theorem)
  uniqueExistsDeclaration = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "∃!"
    let p    =  mkVar "P" $ mkFunctionType alphaType boolType
    let x    =  mkVar "x" alphaType
    let y    =  mkVar "y" alphaType
    py       <- mkApp p y
    px       <- mkApp p x
    xy       <- mkEquality x y
    pyxy     <- mkImplication py xy
    right    <- mkForall "y" alphaType pyxy
    body     <- mkConjunction px right
    ex       <- mkExists "x" alphaType body 
    let defn =  mkLam "P" (mkFunctionType alphaType boolType) ex
    primitiveNewDefinedConstant name defn quantifierType

  uniqueExistsC :: Inference Term
  uniqueExistsC = constantOfDecl uniqueExistsDeclaration

  uniqueExistsD :: Inference Theorem
  uniqueExistsD = theoremOfDecl uniqueExistsDeclaration

  mkUniqueExists :: String -> Type -> Term -> Inference Term
  mkUniqueExists name ty body = do
    uniqueExC <- uniqueExistsC
    let subst =  mkSubstitution [("α", ty)]
    let inst  =  termTypeSubst subst uniqueExC
    let lam   =  mkLam name ty body
    mkApp inst lam

  fromUniqueExists :: Term -> Inference (String, Type, Term)
  fromUniqueExists term = do
    (quantifier, lam) <- fromApp term
    fromLam lam

  --
  -- * Lemmata
  --

  --
  -- ** Reflecting Mosquito's inference rules as theorems
  --

  -- |Produces a derivation of @{} |- forall t. t = t@.
  reflexivityT :: Inference Theorem
  reflexivityT = do
    forallD <- forallD
    let t = mkVar "t" alphaType
    eq    <- mkEquality t t
    conj  <- mkForall "t" alphaType eq
    prf   <- mkConjecture "reflexivity" conj
    prf   <- act prf . Apply $ unfoldConstantP forallD
    prf   <- act prf . Apply $ betaReduceP
    prf   <- act prf . Apply $ abstractP
    prf   <- act prf . Apply $ trueEqualityIntroductionP
    prf   <- act prf . Apply $ alphaP
    qed prf

  -- |Produces a derivation of @{} |- forall t u. t = u ==> u = t@.
  symmetryT :: Inference Theorem
  symmetryT = do
    forallD <- forallD
    implicationD <- implicationD
    conjunctionD <- conjunctionD
    let t   =  mkVar "t" boolType
    let u   =  mkVar "u" boolType
    tu      <- mkEquality t u
    ut      <- mkEquality u t
    body    <- mkImplication tu ut
    conj    <- mkForalls [("t", boolType), ("u", boolType)] body
    prf     <- mkConjecture "symmetry" conj
    prf     <- act prf . Apply $ unfoldConstantP forallD
    prf     <- act prf . Apply $ betaReduceP
    prf     <- act prf . Apply $ abstractP
    prf     <- act prf . Apply $ trueEqualityIntroductionP
    prf     <- act prf . Apply $ abstractP
    prf     <- act prf . Apply $ trueEqualityIntroductionP
    prf     <- act prf . Apply $ implicationIntroductionP
    prf     <- act prf . Apply $ symmetryP
    prf     <- act prf . Apply $ assumeP
    qed prf

  -- |Produces a derivation of @{} |- forall t u v. t = u ==> u = v ==> t = v@.
  transitivityT :: Inference Theorem
  transitivityT = do
    forallD   <- forallD
    [t, u, v] <- mkVars [("t", boolType), ("u", boolType), ("v", boolType)]
    tu        <- mkEquality t u
    uv        <- mkEquality u v
    tv        <- mkEquality t v
    uvtv      <- mkImplication uv tv
    body      <- mkImplication tu uvtv
    conj      <- mkForalls [("t", boolType), ("u", boolType), ("v", boolType)] body
    prf       <- mkConjecture "transitivity" conj
    prf       <- act prf . Apply $ unfoldConstantP forallD
    prf       <- act prf . Apply $ betaReduceP
    prf       <- act prf . repeatN 3 $ Apply abstractP >=> Apply trueEqualityIntroductionP
    prf       <- act prf . repeatN 2 $ Apply implicationIntroductionP
    prf       <- act prf . Apply $ transitivityP u
    prf       <- act prf . repeatN 2 $ Apply assumeP
    qed prf

  -- |Produces a derivation of @{} |- forall t. t ==> t@.
  assumeT :: Inference Theorem
  assumeT = do
    forallD <- forallD
    let t =  mkVar "t" boolType
    tt    <- mkImplication t t
    conj  <- mkForall "t" boolType tt
    prf   <- mkConjecture "assume" conj
    prf   <- act prf . Apply $ unfoldConstantP forallD
    prf   <- act prf . Apply $ betaReduceP
    prf   <- act prf $ Apply abstractP >=> Apply trueEqualityIntroductionP
    prf   <- act prf $ Apply implicationIntroductionP >=> Apply assumeP
    qed prf

  -- |Produces a derivation of @{} |- forall a t u. t = u ==> fn (a:ty). t = fn (a:ty). u@.
  abstractT :: Inference Theorem
  abstractT = do
    forallD   <- forallD
    [a, t, u] <- mkVars [("a", alphaType), ("t", boolType), ("u", boolType)]
    tu        <- mkEquality t u
    let at    =  mkLam "a" alphaType t
    let au    =  mkLam "a" alphaType u
    atau      <- mkEquality at au
    body      <- mkImplication tu atau
    conj      <- mkForalls [("a", alphaType), ("t", boolType), ("u", boolType)] body
    prf       <- mkConjecture "abstract" conj
    prf       <- act prf . Apply $ unfoldConstantP forallD
    prf       <- act prf . Apply $ betaReduceP
    prf       <- act prf . repeatN 3 $ Apply abstractP >=> Apply trueEqualityIntroductionP
    prf       <- act prf $ Apply implicationIntroductionP
    prf       <- act prf . Apply $ abstractP
    prf       <- act prf . Apply $ assumeP
    qed prf

  -- |Produces a derivation of @{} |- forall f g t u. f = g ==> t = u ==> f t = g u@.
  combineT = Mosquito.Utility.Pretty.putStrLn $ do
    forallD <- forallD
    let fvars = [("f", mkFunctionType alphaType betaType), ("g", mkFunctionType alphaType betaType)]
    let avars = [("t", alphaType), ("u", alphaType)]
    [f, g] <- mkVars fvars
    [t, u] <- mkVars avars
    fg     <- mkEquality f g
    tu     <- mkEquality t u
    ft     <- mkApp f t
    gu     <- mkApp g u
    ftgu   <- mkEquality ft gu
    body'  <- mkImplication tu ftgu
    body   <- mkImplication fg body'
    conj   <- mkForalls (fvars ++ avars) body
    prf    <- mkConjecture "combine" conj
    prf       <- act prf . Apply $ unfoldConstantP forallD
    prf       <- act prf . Apply $ betaReduceP
    -- XXX: hit the bug in unfoldConstantP with unification occurs check
    return prf

  --
  -- ** General natural deduction
  --

  -- |Produces a derivation of @{} |- forall t. t /\ true ==> t@.
  conjunctionTrue1T = Mosquito.Utility.Pretty.putStrLn $ do
    trueC   <- trueC
    forallD <- forallD
    let t   =  mkVar "t" boolType
    tTrue   <- mkConjunction t trueC
    body    <- mkImplication tTrue t
    conj    <- mkForall "t" boolType body
    prf     <- mkConjecture "conjunctionTrue1" conj
    prf     <- act prf . Apply $ unfoldConstantP forallD
    prf     <- act prf . Apply $ betaReduceP
    prf     <- act prf . Apply $ abstractP
    prf     <- act prf . Apply $ trueEqualityIntroductionP
    prf     <- act prf . Apply $ implicationIntroductionP
    prf     <- act prf . Apply $ conjunctionElimination2P trueC
    prf     <- act prf . Apply $ assumeP
    qed prf



{-

  -- trueEqIffThm :: Inference Theorem
{-
  trueEqIffThm = Mosquito.Utility.Pretty.putStrLn $ do
    trueC <- trueC
    forallD <- forallD
    let t =  mkVar "t" boolType
    let u =  mkVar "u" boolType
    tu    <- mkEquality t u
    tut   <- mkEquality tu trueC
    body  <- mkEquality tu tut
    conj  <- mkForalls [("t", boolType), ("u", boolType)] body
    prf   <- mkConjecture "trueEqIffThm" conj
    prf   <- act prf . Apply $ unfoldConstantPreTactic forallD
    prf   <- act prf . Apply $ betaReducePreTactic
    prf   <- act prf . repeatN 2 $ Apply abstractPreTactic >=> Apply trueEqIPreTactic
    prf   <- act prf . Apply $ deductAntiSymmetricPreTactic
    prf   <- act prf . Try $ Apply trueEqIPreTactic >=> Apply assumePreTactic
    prf   <- act prf . Apply $ trueEqEPreTactic
    prf <- act prf . Apply $ assumePreTactic
    qed prf
-}


  -- tImpliesTThm :: Inference Theorem
  tImpliesTThm = Mosquito.Utility.Pretty.putStrLn $ do
    forallD      <- forallD
    implicationD <- implicationD
    conjunctionD <- conjunctionD
    let t = mkVar "t" boolType
    body <- mkImplication t t
    conj <- mkForall "t" boolType body
    prf  <- mkConjecture "tImpliesTThm" conj
    prf  <- act prf . Apply $ unfoldConstantPreTactic forallD
    prf  <- act prf . Apply $ betaReducePreTactic
    prf  <- act prf . Apply $ abstractPreTactic
    prf  <- act prf . Apply $ unfoldConstantPreTactic implicationD
    prf  <- act prf . Apply $ betaReducePreTactic
    prf  <- act prf . Apply $ unfoldConstantPreTactic conjunctionD
    prf  <- act prf . Apply $ betaReducePreTactic
    prf    <- act prf . Apply $ trueEqIPreTactic
    return prf

  unfoldConstantsTactic :: [Theorem] -> Tactic
  unfoldConstantsTactic [] = Id
  unfoldConstantsTactic (x:xs) = Apply (unfoldConstantPreTactic x) >=> unfoldConstantsTactic xs

  mkApps :: [Term] -> Inference Term
  mkApps (x:[xs]) = mkApp x xs
  mkApps (x:y:xs)   = do
    head <- mkApp x y
    mkApps $ head:xs
  mkApps _ = fail "makeApps"

{-
  -- symmetryThm :: Inference Theorem
  symmetryThm = Mosquito.Utility.Pretty.putStrLn $ do
    forallD <- forallD
    implicationD <- implicationD
    conjunctionD <- conjunctionD
    let t = mkVar "t" alphaType
    let u = mkVar "u" alphaType
    let k = mkLam "x" boolType . mkLam "y" boolType $ mkVar "x" boolType
    tu    <- mkEquality t u
    ut    <- mkEquality u t
    ktu   <- mkApps [k, tu, ut]
    body  <- mkImplication tu ut
    conj'  <- mkForall "u" alphaType body
    conj   <- mkForall "t" alphaType conj'
    prf    <- mkConjecture "symmetryThm" conj
    prf    <- act prf $ unfoldConstantsTactic [forallD, implicationD, conjunctionD]
    prf    <- act prf . Apply $ betaReducePreTactic
    prf    <- act prf . repeatN 2 $ Apply abstractPreTactic >=> Apply trueEqIPreTactic
    prf    <- act prf . Apply $ deductAntiSymmetricPreTactic
    prf    <- act prf . Try $ Apply abstractPreTactic >=> Apply combinePreTactic
    prf    <- act prf . Try $ Apply trueEqIPreTactic >=> Apply symmetryPreTactic >=> Apply assumePreTactic
    prf    <- act prf . Try $ Apply combinePreTactic >=> Try (Apply alphaPreTactic) >=> Apply trueEqIPreTactic >=> Apply assumePreTactic
    prf    <- act prf . Apply $ trueEqEPreTactic
    prf    <- act prf . Apply $ equalityModusPonensPreTactic ktu
    --prf    <- act prf . Apply $ unfoldConstantPreTactic forallD
    --prf    <- act prf . Apply $ betaReducePreTactic
    --prf    <- act prf . Apply $ abstractPreTactic
    --prf    <- act prf . Apply $ trueEqIPreTactic
    --prf    <- act prf . Apply $ unfoldConstantPreTactic implicationD
    --prf    <- act prf . Apply $ betaReducePreTactic
    --prf    <- act prf . Apply $ unfoldConstantPreTactic conjunctionD
    --prf    <- act prf . Apply $ betaReducePreTactic
    --prf    <- act prf . Apply $ abstractPreTactic
    --prf    <- act prf . Apply $ trueEqIPreTactic
    --prf    <- act prf . Apply $ deductAntiSymmetricPreTactic
    --prf    <- act prf . Try . Apply $ abstractPreTactic
    --prf    <- act prf . Try . Apply $ combinePreTactic
    --prf    <- act prf . Try . Apply $ combinePreTactic
    --prf    <- act prf . Try . Apply $ alphaPreTactic
    --prf    <- act prf . Try . Apply $ trueEqIPreTactic
    --prf    <- act prf . Try . Apply $ assumePreTactic
    --prf    <- act prf . Try $ Apply symmetryPreTactic >=> Apply assumePreTactic
    --prf    <- act prf . Apply $ trueEqEPreTactic
    return prf
-}
-}
-}