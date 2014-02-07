{-# LANGUAGE DoAndIfThenElse #-}

-- |Conversions, possibly failing mappings from terms @t@ to theorems @|- t = u@
--  and conversionals, higher-order functions over conversions.  Conversions
--  and conversionals can be used to implement a simple form of rewriting.
module Mosquito.ProofState.Conversionals (
  -- * The conversion type, and simple conversions
  Conversion,
  failConv, successConv, conversionR,
  -- * Conversionals
  thenConv, repeatConv, elseConv, tryConv,
  -- * Syntax specific conversionals
  combineConv, combineLConv, combineRConv,
  abstractConv,
  -- * More refined conversionals
  unfoldConstantConv,
  replaceEverywhereConv,
  Path(..)
)
where

  import Prelude hiding (fail)

  import qualified Data.Set as S

  import Debug.Trace

  import Mosquito.DerivedRules
  import Mosquito.TermUtilities
  
  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  --
  -- * Simple conversions
  --

  -- |The conversion type, a function that maps terms @t@ to theorems @⊢ t = u@.
  --  This mapping may possibly fail.
  type Conversion = Term -> Inference Theorem

  -- |The conversion that always fails.
  failConv :: Conversion
  failConv term =
    fail . unwords $ [
      "failConv: conversion always fails, supplied term `", pretty term, "'."
    ]

  -- |The conversion that always succeeds (reflexivity).
  successConv :: Conversion
  successConv term = alphaR term term

  -- |Converts a conversion into a rule.
  conversionR :: Conversion -> Theorem -> Inference Theorem
  conversionR conv thm = do
    conv' <- conv . conclusion $ thm
    equalityModusPonensR conv' thm

  --
  -- * Conversionals (conversion valued functionals)
  --

  -- |The sequencing conversional.
  thenConv :: Conversion -> Conversion -> Conversion
  thenConv left right term = do
    thm    <- left term
    (l, r) <- fromEquality . conclusion $ thm
    thm'   <- right r
    transitivityR thm thm'

  -- |The choice conversional.  If the first conversion fails to apply
  --  then the second conversion is applied.
  elseConv :: Conversion -> Conversion -> Conversion
  elseConv left right term =
    inference (left term)
      (const . right $ term)
      return

  -- |Exception handling conversional.  If the first conversion fails to apply,
  --  then the conversion that always succeeds is applied.
  tryConv :: Conversion -> Conversion
  tryConv conv =
    conv `elseConv` successConv

  -- |Repetition of conversion application.
  repeatConv :: Conversion -> Conversion
  repeatConv conv = (conv `thenConv` repeatConv conv) `elseConv` successConv

  --
  -- * Syntax specific conversions
  --

  -- |Apply a conversion to the left hand side of a combination, and
  --  another to the right hand side.
  combineConv :: Conversion -> Conversion -> Conversion
  combineConv leftC rightC term = do
    (left, right) <- fromApp term
    cL            <- leftC left
    cR            <- rightC right
    combineR cL cR

  -- |Specialisation of combineConv which applies a conversion to the
  --  left hand side of a combination, only.
  combineLConv :: Conversion -> Conversion
  combineLConv conv = combineConv conv successConv

  -- |Specialisation of combineConv which applies a conversion to the
  --  right hand side of a combination, only.
  combineRConv :: Conversion -> Conversion
  combineRConv conv = combineConv successConv conv

  -- |Applies a conversion to the body of an abstraction, under the binder.
  abstractConv :: Conversion -> Conversion
  abstractConv conv term = do
    (name, ty, body) <- fromLam term
    c                <- conv body
    abstractR name ty c

  --
  -- * More refined conversionals
  --

  freshenTypesR :: Theorem -> Inference Theorem
  freshenTypesR thm = do
    let cTvs  = typeVars . conclusion $ thm
    let hTvs  = S.unions $ map typeVars . hypotheses $ thm
    let tvs   = S.union cTvs hTvs
    let new   = freshs (length . S.toAscList $ tvs) Nothing tvs
    let base  = zipWith (\x y -> (x, mkTyVar y)) (S.toAscList tvs) new
    let subst = mkSubstitution base
    typeInstantiationR subst thm

  -- |Unfolds a constant with the constant's defining theorem.
  unfoldConstantConv :: Theorem -> Conversion
  unfoldConstantConv thm term =
    if isConst term then do
      thm' <- freshenTypesR thm
      (left, right) <- fromEquality . conclusion $ thm'
      if left == term then do
        typT <- typeOf term
        typR <- typeOf right
        -- XXX: this will not work if alpha is in both types, for instance.
        --      we need to completely freshen the type variables in the theorem
        --      before we unify against the constant, before instantiating
        unif <- unifyTypes typT typR
        thm  <- typeInstantiationR unif thm'
        return thm
      else
        successConv term
    else
      successConv term

  -- |Applies a conversion at every point in a term, rewriting at all positions.
  replaceEverywhereConv :: Conversion -> Conversion
  replaceEverywhereConv conv = go
    where
      go :: Conversion
      go term =
        if isApp term then
          combineConv go go `thenConv` conv $ term
        else if isLam term then do
          abstractConv go `thenConv` conv $ term
        else if isConst term then do
          conv term
        else
          successConv term

  -- |Paths for navigating through terms.
  data Path
    = GoLeft  -- ^Go left through an application.
    | GoRight -- ^Go right through an application.
    | GoUnder -- ^Go under a lambda abstraction.

{-
  pathConv :: [Path] -> Conversion -> Conversion
  pathConv []          conv = return conv
  pathConv (GoLeft:xs) conv =  
-}