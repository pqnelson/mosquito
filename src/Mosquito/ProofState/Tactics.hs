{-# LANGUAGE TemplateHaskell, TypeOperators, DoAndIfThenElse #-}

-- |Implements some basic tactics corresponding to the rules found
--  in the kernel and in the file @DerivedRules.hs@.
module Mosquito.ProofState.Tactics where

  import Prelude hiding (fail)
  
  import Control.Arrow ((***))

  import Mosquito.DerivedRules

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.ProofState

  --
  -- ** Basic tactics
  --

  -- |Tactic that fails immediately with a generic message.
  failTac :: Tactic
  failTac = const $ fail "`failTac'"

  -- |Tactic that fails immediately with a supplied message.
  failWithMessageTac :: String -> Tactic
  failWithMessageTac = const . Fail

  -- |Tactic that doesn't acts as the identity function, making
  --  no changes to the state.
  idTac :: Tactic
  idTac = return

  --
  -- ** Solve outright with a theorem
  --

  -- |@PreTactic@ that solves a goal outright with a theorem.
  solvePreTac :: TheoremPreTactic
  solvePreTac theorem _ concl =
    if conclusion theorem == concl then
      return $ Refine (\[] -> return theorem) []
    else
      fail "`solvePreTac'"

  -- |Lifts @solvePreTac@ to a @Tactic@.
  solveTac :: TheoremTactic
  solveTac = apply . solvePreTac

  --
  -- ** Reflexivity
  --

  -- |@PreTactic@ that solves an equality between two terms
  --  that are alpha-equivalent.
  alphaPreTac :: PreTactic
  alphaPreTac _ concl = do
    (l, r) <- fromEquality concl
    if l == r then do
      theorem <- alpha l r
      return $ Refine (\[] -> return theorem) []
    else
      fail "`alphaPreTac'"

  -- |Lifts @alphaPreTac@ to a @Tactic@.
  alphaTac :: Tactic
  alphaTac = apply alphaPreTac

  -- |@PreTactic@ that solves an equality between two terms
  --  that are syntactically equivalent.  Restricted form of
  --  @alphaPreTac@.
  reflexivityPreTac :: PreTactic
  reflexivityPreTac _ concl = do
    eq <- fromEquality concl
    let (l, r) = (mkStructuralEquality *** mkStructuralEquality) eq
    if l == r then do
      theorem <- reflexivity . fst $ eq
      return $ Refine (\[] -> return theorem) []
    else
      fail "`reflexivityPreTac'"

  -- |Lift @reflexivityPreTac@ to a @Tactic@.
  reflexivityTac :: Tactic
  reflexivityTac = apply reflexivityPreTac

  --
  -- ** Symmetry
  --

  -- |Refines an equality goal, creating a new goal where the sides
  --  of the equality are reversed.
  symmetryPreTac :: PreTactic
  symmetryPreTac assms concl = do
    (l, r) <- fromEquality concl
    nConcl <- mkEquality r l
    return $ Refine (\[t] -> symmetry t) [Open assms nConcl]

  -- |Lifts @symmetryPreTac@ to a @Tactic@.
  symmetryTac :: Tactic
  symmetryTac = apply symmetryPreTac

  --
  -- ** Transitivity
  --

  -- |Refine an equality goal, producing two new equality goals
  --  corresponding to transitivity between the supplied term
  --  and the two sides of the equality of the original goal.
  transitivityPreTac :: TermPreTactic
  transitivityPreTac middle assms concl = do
    (left, right) <- fromEquality concl
    nLeft  <- mkEquality left middle
    nRight <- mkEquality middle right
    return $ Refine (\[t, t'] -> transitivity t t') [Open assms nLeft, Open assms nRight]

  -- |Lifts @transitivityPreTac@ to a @Tactic@.
  transitivityTac :: TermTactic
  transitivityTac = apply . transitivityPreTac

  --
  -- ** Abstract
  --

  -- |Refines an equality goal, stripping lambda bound variables,
  --  creating a new equality goal between the two bodies of the
  --  original goal.  Checks whether the abstracted variables are
  --  the same, if not performs a permutation to make them match.
  abstractPreTac :: PreTactic
  abstractPreTac assms concl = do
    (l, r)             <- fromEquality concl
    (name,  ty, lBody) <- fromLam l
    (name', _,  rBody) <- fromLam r
    if name == name' then do
      nConcl             <- mkEquality lBody rBody
      return $ Refine (\[t] -> abstract name ty t) [Open assms nConcl]
    else do
      let nBody =  permute name name' rBody
      nConcl    <- mkEquality lBody nBody
      return $ Refine (\[t] -> abstract name ty t) [Open assms nConcl]

  -- | Lifts @abstractPreTac@ to a @Tactic@.
  abstractTac :: Tactic
  abstractTac = apply abstractPreTac

  --
  -- ** Combine
  --

  combinePreTac :: PreTactic
  combinePreTac assms concl = do
    (left, right)    <- fromEquality concl
    (leftL, leftR)   <- fromApp left
    (rightL, rightR) <- fromApp right
    nLeft            <- mkEquality leftL rightL
    nRight           <- mkEquality leftR rightR
    return $ Refine (\[t, t'] -> combine t t') [Open assms nLeft, Open assms nRight]

  combineTac :: Tactic
  combineTac = apply combinePreTac

  combineLPreTac :: PreTactic
  combineLPreTac assms concl = do
    (left, right)   <- fromEquality concl
    (leftL, rightL) <- fromApp left
    (leftR, rightR) <- fromApp right
    if leftL == leftR then do
      eq <- mkEquality rightL rightR
      return $ Refine (\[t] -> combineL leftL t) [Open assms eq]
    else
      fail "`combineLTac'"

  combineLTac :: Tactic
  combineLTac = apply combineLPreTac

  combineRPreTac :: PreTactic
  combineRPreTac assms concl = do
    (left, right)    <- fromEquality concl
    (leftL, rightL)  <- fromApp left
    (leftR, rightR) <- fromApp right
    if rightL == rightR then do
      eq <- mkEquality leftL leftR
      return $ Refine (\[t] -> combineR rightL t) [Open assms eq]
    else
      fail "`combineTac"

  combineRTac :: Tactic
  combineRTac = apply combinePreTac

  --
  -- ** Equality modus ponens
  --

  equalityModusPonensPreTac :: TermPreTactic
  equalityModusPonensPreTac guess assms concl = do
    eq <- mkEquality guess concl
    return $ Refine (\[t, t'] -> equalityModusPonens t t') [Open assms eq, Open assms guess]

  equalityModusPonensTac :: TermTactic
  equalityModusPonensTac = apply . equalityModusPonensPreTac

  --
  -- ** Deduct antisymmetric tac
  --

  deductAntiSymmetricPreTac :: PreTactic
  deductAntiSymmetricPreTac assms concl = do
    (left, right) <- fromEquality concl
    let assmsR = right `deleteTheorem` assms
    let assmsL = left `deleteTheorem` assms
    return $ Refine (\[t, t'] -> deductAntiSymmetric t t') [Open assmsL left, Open assmsR right]

  deductAntiSymmetricTac :: Tactic
  deductAntiSymmetricTac = apply deductAntiSymmetricPreTac

  --
  -- ** Beta equivalence
  --

  betaReduce :: Term -> Inference Term
  betaReduce t = do
    (left, right) <- fromApp t
    (n, _, body)  <- fromLam left
    return $ termSubst n right body

  betaReduces :: Term -> Inference Term
  betaReduces t = do
      nT <- betaReduce t
      go nT
    where
      go :: Term -> Inference Term
      go trm = inference (betaReduce trm) (const . return $ trm) go

  betaPreTac :: PreTactic
  betaPreTac _ concl = do
    (left, right) <- fromEquality concl
    reduced       <- betaReduce left
    if reduced == right then do
      thm <- beta left
      return $ Refine (\[] -> return thm) []
    else
      fail "`betaPreTac'"

  betaTac :: Tactic
  betaTac = apply betaPreTac

  betasPreTac :: PreTactic
  betasPreTac _ concl = do
    (left, right) <- fromEquality concl
    reduced       <- betaReduces left
    if reduced == right then do
      thm <- betas left
      return $ Refine (\[] -> return thm) []
    else
      fail "`betasPreTac'"

  betasTac :: Tactic
  betasTac = apply betasPreTac

  reductionPreTac :: PreTactic
  reductionPreTac assms concl = do
    reduced <- betaReduce concl
    equalityModusPonensPreTac reduced assms concl

  reductionTac :: Tactic
  reductionTac = apply reductionPreTac

  --
  -- ** Eta equivalence
  --

  etaPreTac :: PreTactic
  etaPreTac _ concl = do
    (left, _) <- fromEquality concl
    --- XXX: test here
    thm <- eta left
    return $ Refine (\[] -> return thm) []

  etaTac :: Tactic
  etaTac = apply etaPreTac