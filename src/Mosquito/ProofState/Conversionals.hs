module Mosquito.ProofState.Conversionals where

  type Conversion :: Term -> Inference Theorem

  failConv :: Conversion
  failConv term =
    fail . unwords $ [
      "failConv: conversion always fails, supplied term `", pretty term, "'."
    ]

  thenConv :: Conversion -> Conversion -> Conversion
  thenConv left right term = do
    thm    <- left term
    (l, r) <- fromEquality . conclusion $ thm
    thm'   <- right r
    transitivity thm thm'