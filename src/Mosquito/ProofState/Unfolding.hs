{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.ProofState.Unfolding (
  unfoldTactic, pointwiseTactic,
  reductionLocalEdit, reductionPreTactic, reductionTactic
) where

  import Debug.Trace

  import Prelude hiding (fail, repeat)

  import Control.Monad hiding (fail, (>=>))

  import Mosquito.TermUtilities

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.Automation
  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics

  import Mosquito.Utility.Pretty

{-
  data TermPath
    = L -- ^ Go left through an application
    | R -- ^ Go right through an application
    | U -- ^ Go under a lambda-abstraction
    | Y -- ^ Relevant part of the term
    | N -- ^ Ignored part of the term

  unfoldPathTactic :: [TermPath] -> TheoremTactic
  unfoldPathTactic path theorem = apply localPreTactic
    where
      replacePath :: [TermPath] -> ConstantDescription -> Term -> Term -> Inference Term
      replacePath 

      local :: LocalEdit
      local assms concl = do
        userMark ["unfoldPathTactic.local:", pretty theorem, pretty concl]
        (left, right) <- fromEquality . conclusion $ theorem
        if isConst left then do
          constant <- fromConst left
          guess    <- replacePath path constant right concl
          equalityModusPonensLocalEdit guess assms concl
        else if isConst right then do
          constant <- fromConst right
          guess    <- replacePath path constant left concl
          equalityModusPonensLocalEdit guess assms concl
        else
          fail . unwords $ [
            "unfoldPathTactic.local: supplied definitional theorem to be used for"
          , unwords ["unfolding: `", pretty theorem, "' is not an equality between"]
          , "a constant and another term."
          ]
-}


  -- |Unfolds a definition supplied as a theorem and then immediately solves
  --  extraneous subgoals, changing the goal to prove into the original goal
  --  with the constant unfolded.
  unfoldTactic :: TheoremTactic
  unfoldTactic theorem =
      apply localPreTactic >=> pointwiseTactic >=> autoSolveTactic theorem
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
          if constantDescriptionDefinition descr == constantDescriptionDefinition dom then
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

  reductionTactic :: Tactic
  reductionTactic = repeat (apply reductionPreTactic) >=> autoBaseTactic