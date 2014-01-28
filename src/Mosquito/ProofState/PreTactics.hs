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
  deductAntiSymmetricLocalEdit, deductAntiSymmetricPreTactic,
  assumeLocalEdit, assumePreTactic,
  solveLocalEdit, solvePreTactic,
  conversionLocalEdit, conversionPreTactic,
  unfoldConstantPreTactic, betaReducePreTactic
) where

  import Prelude hiding (fail)

  import Data.Label
  import qualified Data.List as L

  import Debug.Trace

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

  alphaLocalEdit :: LocalEdit
  alphaLocalEdit assms concl = do
    userMark ["alphaLocalEdit:", pretty concl]
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
    userMark ["symmetryLocalEdit:", pretty concl]
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
    userMark ["abstractLocalEdit:", pretty concl]
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
    userMark ["combineLocalEdit:", pretty concl]
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
    userMark ["etaLocalEdit:", pretty concl]
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
    let subst     =  mkSubstitution [(n, right)]
    return $ termSubst subst body

  betaLocalEdit :: LocalEdit
  betaLocalEdit _ concl = do
    userMark ["betaLocalEdit:", pretty concl]
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
    userMark ["equalityModusPonensLocalEdit:", pretty guess, pretty concl]
    eq <- mkEquality guess concl
    return $ (\[t, t'] -> equalityModusPonens t t', [(assms, eq), (assms, guess)])

  equalityModusPonensPreTactic :: TermPreTactic
  equalityModusPonensPreTactic guess =
    PreTactic {
      _preTacticName = "equalityModusPonensPreTactic"
    , _localEdit     = equalityModusPonensLocalEdit guess
    }

  deductAntiSymmetricLocalEdit :: LocalEdit
  deductAntiSymmetricLocalEdit assms concl = do
    userMark ["deductAntiSymmetricPreTactic:", pretty concl]
    (left, right) <- fromEquality concl
    return (\[t, t'] -> deductAntiSymmetric t t', [(left:assms, right), (right:assms, left)])

  deductAntiSymmetricPreTactic :: PreTactic
  deductAntiSymmetricPreTactic =
    PreTactic {
      _preTacticName = "deductAntiSymmetricPreTactic"
    , _localEdit     = deductAntiSymmetricLocalEdit
    }

  assumeLocalEdit :: LocalEdit
  assumeLocalEdit assms concl = do
    userMark ["assumeLocalEdit:", pretty concl]
    if concl `L.elem` assms then
      return (\[] -> assume concl, [])
    else
      fail . unwords $ [
        unwords ["assumeLocalEdit: goal `", pretty concl, "' is not amongst the list of"]
      , unwords ["assumption, `", pretty assms, "'."]
      ]

  assumePreTactic :: PreTactic
  assumePreTactic =
    PreTactic {
      _preTacticName = "assumePreTactic"
    , _localEdit     = assumeLocalEdit
    }

  -- * Solving goals outright, and forward proof

  solveLocalEdit :: TheoremLocalEdit
  solveLocalEdit thm _ concl = do
    userMark ["solveLocalEdit:", pretty thm, pretty concl]
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

  conversionLocalEdit :: Conversion -> LocalEdit
  conversionLocalEdit conv assms concl = do
    conv'         <- conv concl
    (left, right) <- fromEquality . conclusion $ conv'
    if left == concl then do
      symm <- symmetry conv'
      return (\[t] -> equalityModusPonens symm t, [(assms, right)])
    else if right == concl then do
      return (\[t] -> equalityModusPonens conv' t, [(assms, left)])
    else
      fail . unwords $ [
        "conversionLocalEdit: supplied conversion produced a bad equation"
      , unwords ["`", pretty conv', "' when applied to goal `", pretty concl, "'."]
      ]

  conversionPreTactic :: Conversion -> PreTactic
  conversionPreTactic conv =
    PreTactic {
      _preTacticName = "conversionPreTactic"
    , _localEdit     = conversionLocalEdit conv
    }

  unfoldConstantPreTactic :: Theorem -> PreTactic
  unfoldConstantPreTactic = conversionPreTactic . replaceAllConv . constConv

  betaReducePreTactic :: PreTactic
  betaReducePreTactic = conversionPreTactic $ replaceAllConv . tryConv $ beta