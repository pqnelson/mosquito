module Mosquito.ProofState.Automation where

  import Prelude hiding (repeat)

  import Control.Monad hiding (fail)

  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics

  autoSolveTactic :: TheoremTactic
  autoSolveTactic thm =
    symmetrise (solveP thm)

  autoBaseTactic :: Tactic
  autoBaseTactic = try (apply alphaP <|> autoEtaTactic <|> autoBetaTactic)
    where
      autoBetaTactic :: Tactic
      autoBetaTactic = symmetrise betaP

      autoEtaTactic :: Tactic
      autoEtaTactic = symmetrise etaP