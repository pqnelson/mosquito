{-# LANGUAGE DoAndIfThenElse #-}

-- |Modules implementing some LCF-style tacticals, for sequencing
--  together, and otherwise combining, tactics, into larger, more
--  complex tactics.
module Mosquito.ProofState.Tacticals (
  -- * Sequencing tacticals
  by,
  -- * Conditional tacticals
  (<|>),
  conditional, conditionalTerm, conditionalTheorem,
  -- * Looping tacticals
  repeatN, repeat,
  -- * Failure handling tacticals
  try
)
where

  import Prelude hiding (repeat)

  import Control.Monad hiding (forever)

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.ProofState
  import Mosquito.ProofState.Tactics

  --
  -- * Sequencing tacticals
  --

  -- |Applies a list of tactics in sequences, with the head
  --  of the list being applied first, second element second,
  --  and so on.
  by :: [Tactic] -> Tactic
  by xs state = foldM (flip ($)) state xs

  --
  -- * Choice tacticals
  --

  infixr <|>

  -- |Applies the first input tactic.  If this tactic fails,
  --  then the result of applying the second input tactic is
  --  returned, otherwise the result of the first is returned.
  (<|>) :: Tactic -> Tactic -> Tactic
  (<|>) l r state =
    case l state of
      Fail{} -> r state
      Success lState -> return lState

  -- |Boolean conditional application, applies the first tactic
  --  if the first argument is @True@, otherwise applies the
  --  second tactic.
  conditional :: Bool -> Tactic -> Tactic -> Tactic
  conditional True  t _ = t
  conditional False _ f = f

  -- |Performs a case split on the first argument, retrieving a
  --  term fed to either the second or third argument, depending
  --  on whether the first argument is @Left@ or @Right@.
  conditionalTerm :: Either Term Term -> TermTactic -> TermTactic -> Tactic
  conditionalTerm (Left t)  l _ = l t
  conditionalTerm (Right t) _ r = r t

  -- |Performs a case split on the first argument, retrieving a
  --  theorem fed to either the second or third argument, depending
  --  on whether the first argument is @Left@ or @Right@.
  conditionalTheorem :: Either Theorem Theorem -> TheoremTactic -> TheoremTactic -> Tactic
  conditionalTheorem (Left t)  l _ = l t
  conditionalTheorem (Right t) _ r = r t

  --
  -- * Repetition
  --

  -- |Repeat application of a tactic a fixed number of times.
  repeatN :: Int -> Tactic -> Tactic
  repeatN 0 _ = idTac
  repeatN m t = t >=> repeatN (m - 1) t

  -- |Repeat application of a tactic indefinitely, returning the last
  --  status upon which the application was successful.
  repeat :: Tactic -> Tactic
  repeat t status =
    case t status of
      Fail err  -> return status
      Success s -> repeat t s

  --
  -- * Failure
  -- 

  -- |Tries to apply its argument to the current state.  If this
  --  results in failure, restores the state prior to application
  --  otherwise returns the updated state.
  try :: Tactic -> Tactic
  try tactic state =
    case tactic state of
      Fail{}    -> return state
      Success s -> return s