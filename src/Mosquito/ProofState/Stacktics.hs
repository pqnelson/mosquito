-- |Stacktics change the current set of open goals in a
--  proof state.
module Mosquito.ProofState.Stacktics (
  selectGoalTac, selectGoalsTac, selectAllGoalsTac,
  selectAllEqualitiesTac,
)
where

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.Tacticals

  selectGoalTac :: Int -> Tactic
  selectGoalTac select =
    selectITac $ (==) select

  selectGoalsTac :: [Int] -> Tactic
  selectGoalsTac select =
    selectITac $ \i -> i `elem` select

  selectAllGoalsTac :: Tactic
  selectAllGoalsTac =
    selectPTac $ const . const $ True

  --
  -- * Syntactic test stackticals
  --

  selectAllEqualitiesTac :: Tactic
  selectAllEqualitiesTac =
    selectPTac $ \_ -> isEquality 