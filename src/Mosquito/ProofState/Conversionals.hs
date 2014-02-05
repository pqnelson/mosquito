{-# LANGUAGE DoAndIfThenElse #-}

module Mosquito.ProofState.Conversionals where

  import Prelude hiding (fail)

  import Debug.Trace

  import Mosquito.DerivedRules
  import Mosquito.TermUtilities
  
  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  type Conversion = Term -> Inference Theorem

  failConv :: Conversion
  failConv term =
    fail . unwords $ [
      "failConv: conversion always fails, supplied term `", pretty term, "'."
    ]

  successConv :: Conversion
  successConv term = alpha term term

  thenConv :: Conversion -> Conversion -> Conversion
  thenConv left right term = do
    thm    <- left term
    (l, r) <- fromEquality . conclusion $ thm
    thm'   <- right r
    transitivity thm thm'

  elseConv :: Conversion -> Conversion -> Conversion
  elseConv left right term =
    inference (left term)
      (const $ right term)
      return

  tryConv :: Conversion -> Conversion
  tryConv conv =
    conv `elseConv` successConv

  repeatConv :: Conversion -> Conversion
  repeatConv conv = (conv `thenConv` repeatConv conv) `elseConv` successConv

  combineConv :: Conversion -> Conversion -> Conversion
  combineConv leftC rightC term = do
    (left, right) <- fromApp term
    cL            <- leftC left
    cR            <- rightC right
    combine cL cR

  combineLConv :: Conversion -> Conversion
  combineLConv conv term = do
    (left, right) <- fromApp term
    c             <- conv left
    combineL right c

  combineRConv :: Conversion -> Conversion
  combineRConv conv term = do
    (left, right) <- fromApp term
    c             <- conv right
    combineR left c

  abstractConv :: Conversion -> Conversion
  abstractConv conv term = do
    (name, ty, body) <- fromLam term
    c                <- conv body
    abstract name ty c

  constConv :: Theorem -> Conversion
  constConv thm term =
    if isConst term then do
      (left, right) <- fromEquality . conclusion $ thm
      if left == term then do
        typT <- typeOf term
        typR <- typeOf right
        -- XXX: this will not work if alpha is in both types, for instance.
        --      we need to completely freshen the type variables in the theorem
        --      before we unify against the constant, before instantiating
        unif <- unifyTypes typT typR
        thm  <- typeInstantiation unif thm
        return thm
      else
        successConv term
    else
      successConv term

  replaceAllConv :: Conversion -> Conversion
  replaceAllConv conv = go
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