{-# LANGUAGE TemplateHaskell, TypeOperators, DoAndIfThenElse #-}

module Mosquito.Tactics where

  import Prelude hiding (fail)

  import Control.Arrow
  import Control.Monad hiding (fail)

  import Data.Label
  import qualified Data.List as L

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  import Mosquito.DerivedRules
  import Mosquito.ProofState

  --
  -- * Tacticals
  --

  (<|>) :: Tactic -> Tactic -> Tactic
  (<|>) left right state =
    inference (left state) (const . right $ state) return

  try :: Tactic -> Tactic
  try tactic state =
    inference (tactic state) (const . return $ state) return

  preceeding :: Tactic -> Tactic -> Tactic
  preceeding = (>=>)

  following :: Tactic -> Tactic -> Tactic
  following = (<=<)

  by :: [Tactic] -> Tactic
  by []     state = return state
  by (x:xs) state = do
    state' <- x state
    by xs state'

  --
  -- * Tactics
  --

  --
  -- ** Alpha-equivalence
  --

  --
  -- ** Solve outright with a theorem
  --

  solvePreTac :: TheoremPreTactic
  solvePreTac theorem assms concl =
    if conclusion theorem == concl then
      return $ Refine (\[] -> return theorem) []
    else
      fail . unwords $ [
        "Theorem passed to `solveTac' does not solve the goal."
      ]

  solveTac :: TheoremTactic
  solveTac = apply . solvePreTac

  --
  -- ** Reflexivity
  --

  simpleReflexivityPreTac :: PreTactic
  simpleReflexivityPreTac assms concl = do
    eq <- fromEquality concl
    let (left, right) = (mkStructuralEquality *** mkStructuralEquality) eq
    if left == right then do
      theorem <- reflexivity . fst $ eq
      return $ Refine (\[] -> return theorem) []
    else
      fail . unwords $ [
        "Terms passed to `simpleReflexivityPreTac' are not structurally"
      , unwords ["equivalent.  Was expecting `", pretty . fst $ eq, "' to"]
      , unwords ["be structurally equivalent to `", pretty . snd $ eq, "'."]
      ]

  simpleReflexivityTac :: Tactic
  simpleReflexivityTac =
      selectCandidates `preceeding` apply simpleReflexivityPreTac
    where
      selectCandidates :: Tactic
      selectCandidates =
        selectPTac (\assms concl -> isEquality concl)

  reflexivityPreTac :: PreTactic
  reflexivityPreTac assms concl = do
    (left, right) <- fromEquality concl
    if left == right then do
      theorem <- reflexivity left
      return $ Refine (\[] -> return theorem) []
    else
      fail "reflexivityTac"

  reflexivityTac :: Tactic
  reflexivityTac = apply reflexivityPreTac

  --
  -- ** Symmetry
  --

  symmetryPreTac :: PreTactic
  symmetryPreTac assms concl = do
    (left, right) <- fromEquality concl
    concl         <- mkEquality right left
    return $ Refine (\[t] -> symmetry t) [Open assms concl]

  symmetryTac :: Tactic
  symmetryTac = apply symmetryPreTac

  --
  -- ** Transitivity
  --

  transitivityPreTac :: TermPreTactic
  transitivityPreTac middle assms concl = do
    (left, right) <- fromEquality concl
    left  <- mkEquality left middle
    right <- mkEquality middle right
    return $ Refine (\[t, t'] -> transitivity t t') [Open assms left, Open assms right]

  transitivityTac :: TermTactic
  transitivityTac = apply . transitivityPreTac

  --
  -- ** Abstract
  --

  abstractPreTac :: PreTactic
  abstractPreTac assms concl = do
    (left, right)     <- fromEquality concl
    (name, ty, leftBody)  <- fromLam left
    (_,     _, rightBody) <- fromLam right
    concl             <- mkEquality leftBody rightBody
    return $ Refine (\[t] -> abstract name ty t) [Open assms concl]

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
    left  <- mkEquality leftL rightL
    right <- mkEquality leftR rightR
    return $ Refine (\[t, t'] -> combine t t') [Open assms left, Open assms right]

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

  betaPreTac :: PreTactic
  betaPreTac assms concl = do
    (left, right) <- fromEquality concl
    -- XXX: test here
    thm <- beta left
    return $ Refine (\[] -> return thm) []

  betaTac :: Tactic
  betaTac = apply betaPreTac

  performBetaRedex :: Term -> Inference Term
  performBetaRedex t = do
    (left, right) <- fromApp t
    (name, ty, body) <- fromLam left
    let subst  = mkSubstitution name right
    let result = termSubst subst body
    return result

  reductionPreTac :: PreTactic
  reductionPreTac assms concl = do
    reduced <- performBetaRedex concl
    equalityModusPonensPreTac reduced assms concl

  reductionTac :: Tactic
  reductionTac =
    by [
      apply reductionPreTac
    , try betaTac
    ]

  etaTac :: PreTactic
  etaTac assms concl = do
    (left, right) <- fromEquality concl
    --- XXX: test here
    thm <- eta left
    return $ Refine (\[] -> return thm) []

  --
  -- ** Unfolding definitions
  --

  unfoldAppLTac :: TheoremTactic
  unfoldAppLTac theorem = apply $ local theorem
    where
      local :: TheoremPreTactic
      local theorem assms concl = do
        (left, right)   <- fromEquality . conclusion $ theorem
        (left', right') <- fromApp concl
        if left == left' then do
          guess <- mkApp right right'
          equalityModusPonensPreTac guess assms concl
        else
          fail $ "unfoldAppLTac"

  --
  -- ** Some simple automation
  --

  baseAuto :: Tactic
  baseAuto =
    reflexivityTac <|>
    apply etaTac <|>
    betaTac 