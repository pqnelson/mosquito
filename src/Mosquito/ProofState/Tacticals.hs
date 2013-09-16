-- |Modules implementing some LCF-style tacticals, for sequencing
--  together, and otherwise combining, tactics, into larger, more
--  complex tactics.
module Mosquito.ProofState.Tacticals (
  -- * Sequencing tacticals
  before, after, by,
  -- * Conditional tacticals
  (<|>),
  conditional, conditionalTerm, conditionalTheorem,
  -- * Looping tacticals
  repeat, forever,
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

  -- |Sequences the first input tactic before the second
  --  input tactic.
  before :: Tactic -> Tactic -> Tactic
  before = (>=>)

  -- |Sequences the second input tactic before the first
  --  input tactic.
  after :: Tactic -> Tactic -> Tactic
  after = (<=<)

  -- |Applies a list of tactics in sequences, with the head
  --  of the list being applied first, second element second,
  --  and so on.
  by :: [Tactic] -> Tactic
  by xs state = foldM (flip ($)) state xs

  --
  -- * Choice tacticals
  --

  -- |Applies the first input tactic.  If this tactic fails,
  --  then the result of applying the second input tactic is
  --  returned, otherwise the result of the first is returned.
  (<|>) :: Tactic -> Tactic -> Tactic
  (<|>) l r state =
    inference (l state) (const . r $ state) return

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
  repeat :: Int -> Tactic -> Tactic
  repeat 0 t = idTac
  repeat m t = t `before` repeat (m - 1) t

  -- |Repeat application of a tactic forever.
  forever :: Tactic -> Tactic
  forever t = t `before` forever t

  --
  -- * Failure
  -- 

  -- |Tries to apply its argument to the current state.  If this
  --  results in failure, restores the state prior to application
  --  otherwise returns the updated state.
  try :: Tactic -> Tactic
  try tactic state =
    inference (tactic state) (const . return $ state) return