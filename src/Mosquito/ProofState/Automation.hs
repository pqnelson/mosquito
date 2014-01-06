module Mosquito.ProofState.Automation where

  import Prelude hiding (repeat)

  import Control.Monad hiding (fail)

  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics

  autoSolveTactic :: TheoremTactic
  autoSolveTactic thm =
    symmetrise (solvePreTactic thm)

  autoBaseTactic :: Tactic
  autoBaseTactic = try (apply alphaPreTactic <|> autoEtaTactic <|> autoBetaTactic)
    where
      autoBetaTactic :: Tactic
      autoBetaTactic = symmetrise betaPreTactic

      autoEtaTactic :: Tactic
      autoEtaTactic = symmetrise etaPreTactic