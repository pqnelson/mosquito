{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.Theories.Boolean (
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
) where

  import Prelude hiding (fail, repeat)

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.ProofState.Automation
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics
  import Mosquito.ProofState.Unfolding

  import Mosquito.Theories.Utility

  import Mosquito.Utility.Extlib
  import Mosquito.Utility.Pretty

  --
  -- ** Logical truth
  --

  -- T = \a : Bool. a = \a : Bool. a
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
    trueC <- trueC
    trueD <- trueD
    conj  <- mkConjecture "trueI" trueC
    conj  <- act conj . unfoldTactic $ trueD
    qed conj

  trueILocalEdit :: LocalEdit
  trueILocalEdit _ concl = do
    userMark ["trueILocalEdit:", pretty concl]
    trueC <- trueC
    if concl == trueC then
      return (\[] -> trueI, [])
    else
      fail . unwords $ [
        "Conclusion passed to `trueIPreTac' not `true'."
      ]

  -- |Solves all goals of the form @true@.
  trueIPreTactic :: PreTactic
  trueIPreTactic = mkPreTactic "trueITactic" trueILocalEdit

  -- |Produces a derivation of @Gamma ⊢ p@ from a derivation of
  --  @Gamma ⊢ p = true@.
  trueEqE :: Theorem -> Inference Theorem
  trueEqE theorem = do
    trueI <- trueI
    symm  <- symmetry theorem
    equalityModusPonens symm trueI

  trueEqELocalEdit :: LocalEdit
  trueEqELocalEdit assms concl = do
    userMark ["trueEqELocalEdit:", pretty concl]
    trueC <- trueC
    eq <- mkEquality concl trueC
    return (\[t] -> trueEqE t, [(assms, eq)])

  trueEqEPreTactic :: PreTactic
  trueEqEPreTactic = mkPreTactic "trueEqEPreTactic" trueEqELocalEdit

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

  trueEqILocalEdit :: LocalEdit
  trueEqILocalEdit assms concl = do
    userMark ["trueEqILocalEdit:", pretty concl]
    trueC <- trueC
    (left, right) <- fromEquality concl
    if right == trueC then do
      return $ (\[t] -> trueEqI t, [(assms, left)])
    else
      fail "`trueEqILocalEdit'"

  trueEqIPreTactic :: PreTactic
  trueEqIPreTactic = mkPreTactic "trueEqIPreTactic" trueEqILocalEdit

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
    let subst = mkSubstitution [("α", ty)]
    let inst =  termTypeSubst subst forallC
    let lam  =  mkLam name ty body
    mkApp inst lam

  fromForall :: Term -> Inference (String, Type, Term)
  fromForall term = do
    (forallC, body) <- fromApp term
    fromLam body

  --
  -- ** Logical falsity
  --

  falseDecl :: Inference (Term, Theorem)
  falseDecl = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "false"
    forallC  <- forallC
    let subst = mkSubstitution [("α", boolType)]
    let inst =  termTypeSubst subst forallC
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

  fromConjunction :: Term -> Inference (Term, Term)
  fromConjunction term = do
    (pre, right)  <- fromApp term
    (conjC, left) <- fromApp pre
    return (left, right)

  {- conjunctionI :: Inference Theorem
  conjunctionIThm left right = Mosquito.Utility.Pretty.putStrLn $ do
      trueC        <- trueC
      conjunctionD <- conjunctionD
      preApp       <- mkApp f (conclusion left)
      app          <- mkApp preApp (conclusion right)
      preApp'      <- mkApp f trueC
      app'         <- mkApp preApp' trueC
      eq           <- mkEquality (mkLam "f" binaryConnectiveType app) (mkLam "f" binaryConnectiveType app')
      conj         <- mkConjunction (conclusion left) (conclusion right)
      prf          <- mkConjecture "conjunctionI" conj
      prf          <-
        act prf . every $ [
          unfoldTactic conjunctionD
        , apply $ equalityModusPonensPreTactic eq
        , try pointwiseTactic
        , try . apply $ trueEqIPreTactic
        , apply symmetryPreTactic
        , try . apply $ beta2PreTactic
        , try . apply $ betaPreTactic
        , try (reductionTactic >=> pointwiseTactic)
        , try (apply symmetryPreTactic >=> apply trueEqIPreTactic)
        , repeat (apply (solvePreTactic left) <|> apply (solvePreTactic right))
        ]
      qed prf
    where
      beta2LocalEdit :: LocalEdit
      beta2LocalEdit assms concl = do
        userMark ["beta2LocalEdit:", pretty concl]
        (left, right) <- fromEquality concl
        (app, arg)    <- fromApp left
        app'          <- betaReduce app
        trm           <- mkApp app' arg
        new           <- mkEquality trm right
        return ((\[t, t'] -> equalityModusPonens t t'), [(assms, trm), (assms, new)])

      beta2PreTactic :: PreTactic
      beta2PreTactic = mkPreTactic "beta2PreTactic" beta2LocalEdit

      f :: Term
      f = mkVar "f" binaryConnectiveType

  test = do
    let true = inference trueI undefined id
    conjunctionIThm true true
  -}

  --
  -- ** Implication
  --

  -- |The declaration and definition of material implication.
  implicationDecl :: Inference (Term, Theorem)
  implicationDecl = do
    let name    =  mkQualifiedName ["Mosquito", "Bool"] "_⇒_"
    let p       =  mkVar "p" boolType
    let q       =  mkVar "q" boolType
    conjunction <- mkConjunction p q
    eq          <- mkEquality conjunction p
    let def     =  mkLam "p" boolType . mkLam "q" boolType $ eq
    primitiveNewDefinedConstant name def binaryConnectiveType

  -- |The implication constant.
  implicationC :: Inference Term
  implicationC = constantOfDecl implicationDecl

  -- |The implication defining theorem.
  implicationD :: Inference Theorem
  implicationD = theoremOfDecl implicationDecl

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
  negationDecl :: Inference (Term, Theorem)
  negationDecl = do
    let name    =  mkQualifiedName ["Mosquito", "Bool"] "¬"
    let a       =  mkVar "a" boolType
    falseC      <- falseC
    implication <- mkImplication a falseC
    let def     =  mkLam "a" boolType implication
    primitiveNewDefinedConstant name def $ mkFunctionType boolType boolType

  -- |The negation constant.
  negationC :: Inference Term
  negationC = constantOfDecl negationDecl

  -- |The negation defining theorem.
  negationD :: Inference Theorem
  negationD = theoremOfDecl negationDecl

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

  -- |The disjunction constant.
  disjunctionC :: Inference Term
  disjunctionC = constantOfDecl disjunctionDecl

  -- |The disjunction defining theorem.
  disjunctionD :: Inference Theorem
  disjunctionD = theoremOfDecl disjunctionDecl

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
  existsDecl :: Inference (Term, Theorem)
  existsDecl = do
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
  existsC = constantOfDecl existsDecl

  -- |The existential quantifier defining theorem.
  existsD :: Inference Theorem
  existsD = theoremOfDecl existsDecl

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

  -- \p q. p ==> q /\ q ==> p
  iffDecl :: Inference (Term, Theorem)
  iffDecl = do
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
  iffC = constantOfDecl iffDecl

  iffD :: Inference Theorem
  iffD = theoremOfDecl iffDecl

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