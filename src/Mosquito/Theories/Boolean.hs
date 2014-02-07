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

  import Mosquito.Theories.Utility

  import Mosquito.Utility.Extlib
  import Mosquito.Utility.Pretty

  --
  -- ** Logical truth
  --

  -- T = \a : Bool. a = \a : Bool. a
  trueDeclaration :: Inference (Term, Theorem)
  trueDeclaration = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "true"
    let t    =  mkLam "a" boolType $ mkVar "a" boolType
    eq       <- mkEquality t t
    primitiveNewDefinedConstant name eq boolType

  trueC :: Inference Term
  trueC = constantOfDecl trueDeclaration

  trueD :: Inference Theorem
  trueD = theoremOfDecl trueDeclaration

  -- |Produces a derivation of @{} ⊢ true@.
  trueIntroductionT :: Inference Theorem
  trueIntroductionT = do
    trueC <- trueC
    trueD <- trueD
    conj  <- mkConjecture "trueIntroduction" trueC
    conj  <- act conj $ Apply (unfoldConstantP trueD)
    conj  <- act conj $ Apply alphaP
    qed conj

  trueIntroductionL :: LocalEdit
  trueIntroductionL _ concl = do
    userMark ["trueIntroductionL:", pretty concl]
    trueC <- trueC
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
    trueC <- trueC
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
    trueC <- trueC
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
{-
let SPEC =
  let P = `P:A->bool`
  and x = `x:A` in
  let pth =
    let th1 = EQ_MP(AP_THM FORALL_DEF `P:A->bool`) (ASSUME `(!)(P:A->bool)`) in
    let th2 = AP_THM (CONV_RULE BETA_CONV th1) `x:A` in
    let th3 = CONV_RULE (RAND_CONV BETA_CONV) th2 in
    DISCH_ALL (EQT_ELIM th3) in
  fun tm th ->
    try let abs = rand(concl th) in
        CONV_RULE BETA_CONV
         (MP (PINST [snd(dest_var(bndvar abs)),aty] [abs,P; tm,x] pth) th)
    with Failure _ -> failwith "SPEC";;
-}
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

  test = Mosquito.Utility.Pretty.putStrLn $ do
    forallEliminationR undefined undefined

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

  conjunctionC :: Inference Term
  conjunctionC = constantOfDecl conjunctionDeclaration

  conjunctionD :: Inference Theorem
  conjunctionD = theoremOfDecl conjunctionDeclaration

  mkConjunction :: Term -> Term -> Inference Term
  mkConjunction left right = do
    conjunctionC <- conjunctionC
    pre          <- mkApp conjunctionC left
    mkApp pre right

  fromConjunction :: Term -> Inference (Term, Term)
  fromConjunction term = do
    (pre, right)  <- fromApp term
    (conjC, left) <- fromApp pre
    return (left, right)

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

  conjunctionIntroductionL :: LocalEdit
  conjunctionIntroductionL assms concl = do
    (left, right) <- fromConjunction concl
    return (\[left, right] -> conjunctionIntroductionR left right, [(assms, left), (assms, right)])

  conjunctionIntroductionP :: PreTactic
  conjunctionIntroductionP = mkPreTactic "conjunctionIntroductionP" conjunctionIntroductionL

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

  conjunctionElimination1L :: Term -> LocalEdit
  conjunctionElimination1L trm assms concl = do
    conj <- mkConjunction trm concl
    return (\[t] -> conjunctionElimination1R t, [(assms, conj)])

  conjunctionElimination1P :: Term -> PreTactic
  conjunctionElimination1P = mkPreTactic "conjunctionElimination1P" . conjunctionElimination1L

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

  conjunctionElimination2L :: Term -> LocalEdit
  conjunctionElimination2L trm assms concl = do
    conj <- mkConjunction concl trm
    return (\[t] -> conjunctionElimination2R t, [(assms, conj)])

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

  fromImplication :: Term -> Inference (Term, Term)
  fromImplication term = do
    (pre, right) <- fromApp term
    (impC, left) <- fromApp pre
    return (left, right)

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

  implicationEliminationL :: Term -> LocalEdit
  implicationEliminationL trm assms concl = do
    imp <- mkImplication trm concl
    return (\[left, right] -> implicationEliminationR left right, [(assms, imp), (assms, trm)])

  implicationEliminationP :: Term -> PreTactic
  implicationEliminationP = mkPreTactic "implicationEliminationP" . implicationEliminationL

{-
let DISCH =
  let p = `p:bool`
  and q = `q:bool` in
  let pth = SYM(BETA_RULE (AP_THM (AP_THM IMP_DEF p) q)) in
  fun a th ->
    let th1 = CONJ (ASSUME a) th in
    let th2 = CONJUNCT1 (ASSUME (concl th1)) in
    let th3 = DEDUCT_ANTISYM_RULE th1 th2 in
    let th4 = INST [a,p; concl th,q] pth in
    EQ_MP th4 th3;;
-}
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

  implicationIntroductionL :: LocalEdit
  implicationIntroductionL assms concl = do
    (left, right) <- fromImplication concl
    return (\[t] -> implicationIntroductionR left t, [(left:assms, right)])

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

  fromNegation :: Term -> Inference Term
  fromNegation term = do
    (negC, body) <- fromApp term
    return body

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
    prf   <- mkConjecture "reflexivityThm" conj
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