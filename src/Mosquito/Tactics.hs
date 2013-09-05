{-# LANGUAGE TemplateHaskell, TypeOperators, DoAndIfThenElse #-}

module Mosquito.Tactics where

  import Prelude hiding (fail)

  import Control.Monad hiding (fail)

  import Data.Label
  import qualified Data.List as L

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  import Mosquito.ProofState

  --
  -- * Tacticals
  --

  inference :: Inference b -> (String -> a) -> (b -> a) -> a
  inference (Fail err) f s = f err
  inference (Success ok) f s = s ok

  (<|>) :: Tactic -> Tactic -> Tactic
  (<|>) left right state =
    inference (left state) (const $ right state) return

  try :: Tactic -> Tactic
  try tactic state =
    inference (tactic state) (const $ return state) return

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
    let assmsL = right `deleteTheorem` assms
    let assmsR = left `deleteTheorem` assms
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