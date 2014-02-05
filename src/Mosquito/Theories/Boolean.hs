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
    conjunctionD <- conjunctionD
    conj         <- mkConjunction (conclusion left) (conclusion right)
    prf          <- mkConjectureRule "conjunctionIntroduction" (hypotheses left ++ hypotheses right) conj
    prf          <- act prf . Apply $ unfoldConstantP conjunctionD
    prf          <- act prf . Apply $ betaReduceP
    prf          <- act prf . Apply $ alphaP
    qed prf

  conjunctionIntroductionL :: LocalEdit
  conjunctionIntroductionL assms concl = do
    (left, right) <- fromConjunction concl
    return (\[left, right] -> conjunctionIntroductionR left right, [(assms, left), (assms, right)])

  conjunctionIntroductionP :: PreTactic
  conjunctionIntroductionP = mkPreTactic "conjunctionIntroductionP" conjunctionIntroductionL

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
  -- * Misc
  --
  -- | Produces a derivation of @{} ⊢ forall t. t = t@.
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