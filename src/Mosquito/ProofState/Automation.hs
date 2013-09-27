module Mosquito.ProofState.Automation where

  import Prelude hiding (repeat)

  import Control.Monad hiding (fail)

  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.Tactics
  import Mosquito.ProofState.Tacticals

  autoSolve :: TheoremTactic
  autoSolve thm =
    solveTac thm <|> symmetryTac >=> solveTac thm

  autoBase :: Tactic
  autoBase = repeat $ alphaTac <|> autoEtaTac <|> autoBetaTac
    where
      autoBetaTac :: Tactic
      autoBetaTac = betaTac <|> (symmetryTac >=> betaTac)

      autoEtaTac :: Tactic
      autoEtaTac = etaTac <|> (symmetryTac >=> etaTac)