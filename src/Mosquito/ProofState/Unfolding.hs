{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.ProofState.Unfolding where

  import Prelude hiding (fail, repeat)

  import Control.Monad hiding (fail)

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.Automation
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.Tactics
  import Mosquito.ProofState.Tacticals

  -- |Unfolds a definition supplied as a theorem and then immediately solves
  --  extraneous subgoals, changing the goal to prove into the original goal
  --  with the constant unfolded.
  unfoldTac :: TheoremTactic
  unfoldTac theorem = apply local >=> pointwiseTac >=> (try $ autoSolve theorem)
    where
      replace :: ConstantDescription -> Term -> Term -> Inference Term
      replace dom rng t =
        if isApp t then do
          (l, r) <- fromApp t
          nL     <- replace dom rng l
          nR     <- replace dom rng r
          mkApp nL nR
        else if isLam t then do
          (n, ty, body) <- fromLam t
          nBody <- replace dom rng body
          return $ mkLam n ty nBody
        else if isConst t then do
          descr <- fromConst t
          if descr == dom then
            return rng
          else
            return t
        else return t

      local :: PreTactic
      local assms concl = do
        (left, right) <- fromEquality . conclusion $ theorem
        if isConst left then do
          c     <- fromConst left
          guess <- replace c right concl
          equalityModusPonensPreTac guess assms concl
        else if isConst right then do
          c     <- fromConst right
          guess <- replace c left concl
          equalityModusPonensPreTac guess assms concl
        else
          fail "`unfoldTac'"

  -- |Decompose an equality between terms into equalities between subterms,
  --  solving easy goals with automation.
  pointwiseTac :: Tactic
  pointwiseTac = repeat (abstractTac <|> combineTac) >=> try autoBase

  -- |Performs a beta-reduction of the goal, immediately closing extraneous
  --  subgoals with automation.
  reductionPreTac :: PreTactic
  reductionPreTac assms concl = do
    reduced <- betaReduce concl
    equalityModusPonensPreTac reduced assms concl

  reductionTac :: Tactic
  reductionTac = repeat $ apply reductionPreTac >=> autoBase