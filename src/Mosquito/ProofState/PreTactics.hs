{-# LANGUAGE TemplateHaskell, DoAndIfThenElse #-}

-- |Implements some basic tactics corresponding to the rules found
--  in the kernel and in the file @DerivedRules.hs@.
module Mosquito.ProofState.PreTactics (
  Justification,
  LocalEdit, TermLocalEdit, TheoremLocalEdit,
  PreTactic, TermPreTactic, TheoremPreTactic,
  preTacticName, localEdit, mkPreTactic,
  alphaLocalEdit, alphaPreTactic,
  symmetryLocalEdit, symmetryPreTactic,
  betaReduce, betaLocalEdit, betaPreTactic,
  etaLocalEdit, etaPreTactic,
  abstractLocalEdit, abstractPreTactic,
  combineLocalEdit, combinePreTactic,
  equalityModusPonensLocalEdit, equalityModusPonensPreTactic,
  solveLocalEdit, solvePreTactic
) where

  import Prelude hiding (fail)

  import Data.Label

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  -- * Tactic types and representation

  type Justification    = [Theorem] -> Inference Theorem
  type LocalEdit        = [Theorem] -> Term -> Inference (Justification, [([Theorem], Term)])
  type TermLocalEdit    = Term -> LocalEdit
  type TheoremLocalEdit = Theorem -> LocalEdit

  data PreTactic
    = PreTactic {
      _preTacticName :: String
    , _localEdit     :: LocalEdit
    }

  mkLabels [''PreTactic]

  mkPreTactic :: String -> LocalEdit -> PreTactic
  mkPreTactic = PreTactic

  instance Pretty PreTactic where
    pretty = get preTacticName


  type TermPreTactic    = Term -> PreTactic
  type TheoremPreTactic = Theorem -> PreTactic

  -- * Basic tactics

  alphaLocalEdit :: LocalEdit
  alphaLocalEdit assms concl = do
    (left, right) <- fromEquality concl
    if left == right then do
      return $ (\[] -> alpha left right, [])
    else
      fail . unwords $ [
        "alphaLocalEdit: left and right side of equality not alpha-equivalent"
      , unwords ["when testing terms `", pretty left, "'' and `", pretty right, "'."]
      ]

  alphaPreTactic :: PreTactic
  alphaPreTactic =
    PreTactic {
      _preTacticName = "alphaPreTactic"
    , _localEdit     = alphaLocalEdit
    }

  symmetryLocalEdit :: LocalEdit
  symmetryLocalEdit assms concl = do
    (l, r) <- fromEquality concl
    nConcl <- mkEquality r l
    return $ (\[t] -> symmetry t, [(assms, nConcl)])

  symmetryPreTactic :: PreTactic
  symmetryPreTactic =
    PreTactic {
      _preTacticName = "symmetryTactic"
    , _localEdit     = symmetryLocalEdit
    }

  abstractLocalEdit :: LocalEdit
  abstractLocalEdit assms concl = do
    (l, r)             <- fromEquality concl
    (name,  ty, lBody) <- fromLam l
    (name', _,  rBody) <- fromLam r
    if name == name' then do
      nConcl <- mkEquality lBody rBody
      return (\[t] -> abstract name ty t, [(assms, nConcl)])
    else do
      let nBody =  permute name name' rBody
      nConcl    <- mkEquality lBody nBody
      return (\[t] -> abstract name ty t, [(assms, nConcl)])

  abstractPreTactic :: PreTactic
  abstractPreTactic =
    PreTactic {
      _preTacticName = "abstractPreTactic"
    , _localEdit     = abstractLocalEdit
    }

  combineLocalEdit :: LocalEdit
  combineLocalEdit assms concl = do
    (left, right)   <- fromEquality concl
    (leftL, rightL) <- fromApp left
    (leftR, rightR) <- fromApp right
    nLeft           <- mkEquality leftL leftR
    nRight          <- mkEquality rightL rightR
    return (\[t, t'] -> combine t t', [(assms, nLeft), (assms, nRight)])

  combinePreTactic :: PreTactic
  combinePreTactic =
    PreTactic {
      _preTacticName = "combinePreTactic"
    , _localEdit     = combineLocalEdit
    }

  etaLocalEdit :: LocalEdit
  etaLocalEdit _ concl = do
    (left, _) <- fromEquality concl
    --- XXX: test here
    thm <- eta left
    return $ (\[] -> return thm, [])

  etaPreTactic :: PreTactic
  etaPreTactic =
    PreTactic {
      _preTacticName = "etaPreTactic"
    , _localEdit     = etaLocalEdit
    }

  betaReduce :: Term -> Inference Term
  betaReduce t = do
    (left, right) <- fromApp t
    (n, _, body)  <- fromLam left
    return $ termSubst n right body

  betaLocalEdit :: LocalEdit
  betaLocalEdit _ concl = do
    (left, right) <- fromEquality concl
    reduced       <- betaReduce left
    if reduced == right then do
      thm <- beta left
      return $ (\[] -> return thm, [])
    else
      fail . unwords $ [
        "betaLocalEdit: beta reduced left hand side"
      ]

  betaPreTactic :: PreTactic
  betaPreTactic =
    PreTactic {
      _preTacticName = "betaPreTactic"
    , _localEdit     = betaLocalEdit
    }

  equalityModusPonensLocalEdit :: TermLocalEdit
  equalityModusPonensLocalEdit guess assms concl = do
    eq <- mkEquality guess concl
    return $ (\[t, t'] -> equalityModusPonens t t', [(assms, eq), (assms, guess)])

  equalityModusPonensPreTactic :: TermPreTactic
  equalityModusPonensPreTactic guess =
    PreTactic {
      _preTacticName = "equalityModusPonensPreTactic"
    , _localEdit     = equalityModusPonensLocalEdit guess
    }

  -- * Solving goals outright, and forward proof

  solveLocalEdit :: TheoremLocalEdit
  solveLocalEdit thm _ concl =
    if conclusion thm == concl then
      return (\[] -> return thm, [])
    else
      fail . unwords $ [
        unwords ["solveLocalEdit: conclusion of supplied theorem `", pretty thm, "'"]
      , "does not match goal."
      ]

  solvePreTactic :: TheoremPreTactic
  solvePreTactic thm =
    PreTactic {
      _preTacticName = "solvePreTactic"
    , _localEdit     = solveLocalEdit thm
    }