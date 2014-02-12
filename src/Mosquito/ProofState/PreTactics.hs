{-# LANGUAGE TemplateHaskell, DoAndIfThenElse #-}

-- |Implements some basic tactics corresponding to the rules found
--  in the kernel and in the file @DerivedRules.hs@.
module Mosquito.ProofState.PreTactics (
  Justification,
  LocalEdit, TermLocalEdit, TheoremLocalEdit,
  PreTactic, TermPreTactic, TheoremPreTactic,
  preTacticName, localEdit, mkPreTactic,
  alphaL, alphaP,
  symmetryL, symmetryP,
  transitivityL, transitivityP,
  abstractL, abstractP,
  combineL, combineP,
  betaL, betaP,
  etaL, etaP,
  equalityModusPonensL, equalityModusPonensP,
  assumeL, assumeP,
  solveL, solveP,
  conversionL, conversionP,
  unfoldConstantP, betaReduceP, etaReduceP
) where

  import Prelude hiding (fail)

  import Data.Label
  import qualified Data.List as L

  import Debug.Trace

  import Mosquito.TermUtilities

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.Conversionals

  import Mosquito.Utility.Pretty

  -- * Tactic types and representation

  type Justification    = [Theorem] -> Inference Theorem
  type LocalEdit        = [Term] -> Term -> Inference (Justification, [([Term], Term)])
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

  alphaL :: LocalEdit
  alphaL assms concl = do
    userMark ["alphaL:", pretty concl]
    if isEquality concl then do
      (left, right) <- fromEquality concl
      if left == right then do
        return $ (\[] -> alphaR left right, [])
      else
        fail . unwords $ [
          "alphaL: left and right side of equality not alpha-equivalent"
        , unwords ["when testing terms `", pretty left, "'' and `", pretty right, "'."]
        ]
    else
      fail . unwords $ [
        "alphaL: goal `", pretty concl, "' is not an equality."
      ]

  alphaP :: PreTactic
  alphaP =
    PreTactic {
      _preTacticName = "alphaP"
    , _localEdit     = alphaL
    }

  symmetryL :: LocalEdit
  symmetryL assms concl = do
    userMark ["symmetryL:", pretty concl]
    if isEquality concl then do
      (l, r) <- fromEquality concl
      nConcl <- mkEquality r l
      return $ (\[t] -> symmetryR t, [(assms, nConcl)])
    else
      fail . unwords $ [
        "symmetryL: goal `", pretty concl, "' is not an equality."
      ]

  symmetryP :: PreTactic
  symmetryP =
    PreTactic {
      _preTacticName = "symmetryP"
    , _localEdit     = symmetryL
    }

  transitivityL :: Term -> LocalEdit
  transitivityL middle assms concl = do
    userMark ["transitivityL:", pretty middle, pretty concl]
    if isEquality concl then do
      (l, r) <- fromEquality concl
      nL     <- mkEquality l middle
      nR     <- mkEquality middle r
      return (\[t, t'] -> transitivityR t t', [(assms, nL), (assms, nR)])
    else
      fail . unwords $ [
        "transitivityL: goal `", pretty concl, "' is not an equality."
      ]

  transitivityP :: Term -> PreTactic
  transitivityP middle =
    PreTactic {
      _preTacticName = "transitivityP"
    , _localEdit     = transitivityL middle
    }

  abstractL :: LocalEdit
  abstractL assms concl = do
    userMark ["abstractL:", pretty concl]
    if isEquality concl then do
      (l, r)             <- fromEquality concl
      if isLam l && isLam r then do
        (name,  ty, lBody) <- fromLam l
        (name', _,  rBody) <- fromLam r
        if name == name' then do
          nConcl <- mkEquality lBody rBody
          return (\[t] -> abstractR name ty t, [(assms, nConcl)])
        else do
          let nBody =  permute name name' rBody
          nConcl    <- mkEquality lBody nBody
          return (\[t] -> abstractR name ty t, [(assms, nConcl)])
      else
        fail . unwords $ [
          "abstractL: goal `", pretty concl, "' must be an equality between lambda-abstractions."
        ]
    else
      fail . unwords $ [
        "abstractL: goal `", pretty concl, "' is not an equality."
      ]

  abstractP :: PreTactic
  abstractP =
    PreTactic {
      _preTacticName = "abstractP"
    , _localEdit     = abstractL
    }

  combineL :: LocalEdit
  combineL assms concl = do
    userMark ["combineL:", pretty concl]
    if isEquality concl then do
      (left, right)   <- fromEquality concl
      if isApp left && isApp right then do
        (leftL, rightL) <- fromApp left
        (leftR, rightR) <- fromApp right
        nLeft           <- mkEquality leftL leftR
        nRight          <- mkEquality rightL rightR
        return (\[t, t'] -> combineR t t', [(assms, nLeft), (assms, nRight)])
      else
        fail . unwords $ [
          "combineL: goal `", pretty concl, "' must be an equality between applications."
        ]
    else
      fail . unwords $ [
        "combineL: goal `", pretty concl, "' must be an equality."
      ]

  combineP :: PreTactic
  combineP =
    PreTactic {
      _preTacticName = "combineP"
    , _localEdit     = combineL
    }

  etaL :: LocalEdit
  etaL _ concl = do
    userMark ["etaL:", pretty concl]
    if isEquality concl then do
      (left, right) <- fromEquality concl
      if isEtaContractum left right then
        return $ (\[] -> etaR left, [])
      else
        fail . unwords $ [
          "etaL: goal `", pretty concl, "' must be an equality between an eta redex"
        , "and its contractum."
        ]
    else
      fail . unwords $ [
        "etaL: goal `", pretty concl, "' must be an equality."
      ]

  etaP :: PreTactic
  etaP =
    PreTactic {
      _preTacticName = "etaP"
    , _localEdit     = etaL
    }

  betaReduce :: Term -> Inference Term
  betaReduce t = do
    (left, right) <- fromApp t
    (n, _, body)  <- fromLam left
    let subst     =  mkSubstitution [(n, right)]
    return $ termSubst subst body

  betaL :: LocalEdit
  betaL _ concl = do
    userMark ["betaL:", pretty concl]
    if isEquality concl then do
      (left, right) <- fromEquality concl
      if isBetaContractum left right then
        return $ (\[] -> betaR left, [])
      else
        fail . unwords $ [
          unwords ["betaL: goal `", pretty concl, "' must be an equality between a"]
        , "beta redex and its contractum."
        ]
    else
      fail . unwords $ [
        "betaL: goal `", pretty concl, "' must be an equality."
      ]

  betaP :: PreTactic
  betaP =
    PreTactic {
      _preTacticName = "betaP"
    , _localEdit     = betaL
    }

  equalityModusPonensL :: TermLocalEdit
  equalityModusPonensL guess assms concl = do
    userMark ["equalityModusPonensL:", pretty guess, pretty concl]
    eq <- mkEquality guess concl
    return $ (\[t, t'] -> equalityModusPonensR t t', [(assms, eq), (assms, guess)])

  equalityModusPonensP :: TermPreTactic
  equalityModusPonensP guess =
    PreTactic {
      _preTacticName = "equalityModusPonensP"
    , _localEdit     = equalityModusPonensL guess
    }

  assumeL :: LocalEdit
  assumeL assms concl = do
    userMark ["assumeL:", pretty concl]
    if concl `L.elem` assms then
      return (\[] -> assumeR concl, [])
    else
      fail . unwords $ [
        unwords ["assumeL: goal `", pretty concl, "' is not amongst the list of"]
      , unwords ["assumption, `", pretty assms, "'."]
      ]

  assumeP :: PreTactic
  assumeP =
    PreTactic {
      _preTacticName = "assumeP"
    , _localEdit     = assumeL
    }

  -- * Solving goals outright, and forward proof

  solveL :: TheoremLocalEdit
  solveL thm _ concl = do
    userMark ["solveL:", pretty thm, pretty concl]
    if conclusion thm == concl then
      return (\[] -> return thm, [])
    else
      fail . unwords $ [
        unwords ["solveL: conclusion of supplied theorem `", pretty thm, "'"]
      , "does not match goal."
      ]

  solveP :: TheoremPreTactic
  solveP thm =
    PreTactic {
      _preTacticName = "solveP"
    , _localEdit     = solveL thm
    }

  conversionL :: Conversion -> LocalEdit
  conversionL conv assms concl = do
    conv'         <- conv concl
    (left, right) <- fromEquality . conclusion $ conv'
    if left == concl then do
      symm <- symmetryR conv'
      return (\[t] -> equalityModusPonensR symm t, [(assms, right)])
    else if right == concl then do
      return (\[t] -> equalityModusPonensR conv' t, [(assms, left)])
    else
      fail . unwords $ [
        "conversionL: supplied conversion produced a bad equation"
      , unwords ["`", pretty conv', "' when applied to goal `", pretty concl, "'."]
      ]

  conversionP :: Conversion -> PreTactic
  conversionP conv =
    PreTactic {
      _preTacticName = "conversionP"
    , _localEdit     = conversionL conv
    }

  unfoldConstantP :: Theorem -> PreTactic
  unfoldConstantP = conversionP . replaceEverywhereConv . unfoldConstantConv

  betaReduceP :: PreTactic
  betaReduceP = conversionP . replaceEverywhereConv . tryConv $ betaR

  etaReduceP :: PreTactic
  etaReduceP = conversionP . replaceEverywhereConv . tryConv $ etaR