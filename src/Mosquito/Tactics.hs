{-# LANGUAGE TemplateHaskell, TypeOperators, DoAndIfThenElse #-}

module Mosquito.Tactics where

  import Prelude hiding (fail)

  import Data.Label
  import qualified Data.List as L

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  import Mosquito.ProofState

  try :: PreTactic -> PreTactic
  try tactic assms concl =
    case tactic assms concl of
      Fail{}    -> return $ Open assms concl
      Success t -> return t

  (<|>) :: PreTactic -> PreTactic -> PreTactic
  (<|>) left right assms concl =
    case left assms concl of
      Fail{}    -> right assms concl
      Success t -> return t

  subsequently :: PreTactic -> PreTactic -> PreTactic
  subsequently left right assms concl =
    case left assms concl of
      f@Fail{}  -> f
      Success t ->
        case t of
          Open assms' concl' -> right assms concl'
          t@Refine{} -> return t

  solveTac :: TheoremPreTactic
  solveTac proposed assms concl =
    if conclusion proposed == concl then
      return $ Refine (\[] -> return proposed) []
    else
      fail . unwords $ [
        "Theorem passed to `solveTac' does not solve the goal."
      ]
  reflexivityTac :: PreTactic
  reflexivityTac assms concl = do
    (left, right) <- fromEquality concl
    if left == right then do
      thm <- reflexivity left
      return $ Refine (\[] -> return thm) []
    else
      fail "reflexivityTac"

  symmetryTac :: PreTactic
  symmetryTac assms concl = do
    (left, right) <- fromEquality concl
    concl         <- mkEquality right left
    return $ Refine (\[t] -> symmetry t) [Open assms concl]

  transitivityTac :: TermPreTactic
  transitivityTac middle assms concl = do
    (left, right) <- fromEquality concl
    left  <- mkEquality left middle
    right <- mkEquality middle right
    return $ Refine (\[t, t'] -> transitivity t t') [Open assms left, Open assms right]

  abstractTac :: PreTactic
  abstractTac assms concl = do
    (left, right)     <- fromEquality concl
    (name, ty, leftBody)  <- fromLam left
    (_,     _, rightBody) <- fromLam right
    concl             <- mkEquality leftBody rightBody
    return $ Refine (\[t] -> abstract name ty t) [Open assms concl]

  combineTac :: PreTactic
  combineTac assms concl = do
    (left, right)    <- fromEquality concl
    (leftL, leftR)   <- fromApp left
    (rightL, rightR) <- fromApp right
    left  <- mkEquality leftL rightL
    right <- mkEquality leftR rightR
    return $ Refine (\[t, t'] -> combine t t') [Open assms left, Open assms right]

  equalityModusPonensTac :: TermPreTactic
  equalityModusPonensTac guess assms concl = do
    eq <- mkEquality guess concl
    return $ Refine (\[t, t'] -> equalityModusPonens t t') [Open assms eq, Open assms guess]

  betaTac :: PreTactic
  betaTac assms concl = do
    (left, right) <- fromEquality concl
    -- XXX: test here
    thm <- beta left
    return $ Refine (\[] -> return thm) []

  etaTac :: PreTactic
  etaTac assms concl = do
    (left, right) <- fromEquality concl
    --- XXX: test here
    thm <- eta left
    return $ Refine (\[] -> return thm) []

  baseAuto :: PreTactic
  baseAuto =
    reflexivityTac <|>
    etaTac <|>
    betaTac 