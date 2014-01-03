{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.ProofState.Unfolding where

  import Prelude hiding (fail, repeat)

  import Control.Monad hiding (fail, (>=>))

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.Automation
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics

  -- |Unfolds a definition supplied as a theorem and then immediately solves
  --  extraneous subgoals, changing the goal to prove into the original goal
  --  with the constant unfolded.
  unfoldTac :: TheoremTactic
  unfoldTac theorem = apply localPreTactic >=> pointwiseTactic >=> (try $ autoSolveTactic theorem)
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

      local :: LocalEdit
      local assms concl = do
        (left, right) <- fromEquality . conclusion $ theorem
        if isConst left then do
          c     <- fromConst left
          guess <- replace c right concl
          equalityModusPonensLocalEdit guess assms concl
        else if isConst right then do
          c     <- fromConst right
          guess <- replace c left concl
          equalityModusPonensLocalEdit guess assms concl
        else
          fail "`unfoldTac'"

      localPreTactic = mkPreTactic "unfoldTac.local" local

  -- |Decompose an equality between terms into equalities between subterms,
  --  solving easy goals with automation.
  pointwiseTactic :: Tactic
  pointwiseTactic = repeat (apply abstractPreTactic <|> apply combinePreTactic) >=> autoBaseTactic

  -- |Performs a beta-reduction of the goal, immediately closing extraneous
  --  subgoals with automation.
  reductionLocalEdit :: LocalEdit
  reductionLocalEdit assms concl = do
    reduced <- betaReduce concl
    equalityModusPonensLocalEdit reduced assms concl

  reductionPreTactic :: PreTactic
  reductionPreTactic = mkPreTactic "reductionPreTactic" reductionLocalEdit

  reductionTac :: Tactic
  reductionTac = repeat (apply reductionPreTactic) >=> autoBaseTactic