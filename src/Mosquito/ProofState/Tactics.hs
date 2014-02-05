{-# LANGUAGE GADTs #-}

module Mosquito.ProofState.Tactics (
  Tactic(..),
  TheoremTactic, TermTactic,
  (<|>), (>=>),
  apply, try, every, repeat, repeatN,
  symmetrise,
  optimise
) where

  import Prelude hiding (fail, repeat, id)

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.PreTactics

  data Tactic where
    Apply       :: PreTactic -> Tactic
    FollowedBy  :: Tactic    -> Tactic -> Tactic
    Id          :: Tactic
    FailWith    :: String    -> Tactic
    Try         :: Tactic    -> Tactic
    Choice      :: Tactic    -> Tactic -> Tactic
    Repeat      :: Tactic    -> Tactic
    SelectGoalI :: Int       -> Tactic

  type TheoremTactic = Theorem -> Tactic
  type TermTactic    = Term    -> Tactic

  apply :: PreTactic -> Tactic
  apply = Apply

  (<|>) :: Tactic -> Tactic -> Tactic
  (<|>) = Choice

  try :: Tactic -> Tactic
  try = Try

  id :: Tactic
  id = Id

  fail :: Tactic
  fail = FailWith ""

  failWith :: String -> Tactic
  failWith = FailWith

  (>=>) :: Tactic -> Tactic -> Tactic
  (>=>) = FollowedBy

  repeat :: Tactic -> Tactic
  repeat = Repeat

  repeatN :: Int -> Tactic -> Tactic
  repeatN 0 tactic = Id
  repeatN m tactic = tactic >=> repeatN (m - 1) tactic

  every :: [Tactic] -> Tactic
  every = foldr (>=>) Id

  -- * Useful lifting

  symmetrise :: PreTactic -> Tactic
  symmetrise pretactic = apply pretactic <|> (apply symmetryPreTactic >=> apply pretactic)

  -- * Rejigging tactics based on equational reasoning

  optimise :: Tactic -> Tactic
  optimise (FollowedBy Id               tactic)         = optimise tactic
  optimise (FollowedBy tactic           Id)             = optimise tactic
  optimise (FollowedBy (FailWith err)   tactic)         = FailWith err
  optimise (FollowedBy tactic           (FailWith err)) = FailWith err
  optimise (Choice     (FailWith err)   tactic)         = optimise tactic
  optimise (Choice     tactic           (FailWith err)) = optimise tactic
  optimise (Choice     Id               tactic)         = optimise tactic
  optimise (Repeat     (FailWith err))                  = Id
  optimise (Repeat     (Repeat tactic))                 = optimise . Repeat . optimise $ tactic
  optimise (Try        (Try tactic))                    = optimise . Try . optimise $ tactic
  optimise tactic                                       = tactic