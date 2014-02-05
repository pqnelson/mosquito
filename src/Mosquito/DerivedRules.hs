{-# LANGUAGE ViewPatterns #-}

-- |Derived, useful theorems --- direct consequences of the primitive inference
--  rules defined in the kernel.
module Mosquito.DerivedRules (
  -- * Reflexivity
  reflexivityR,
  -- * Restricted combination rules
  combineLeftR, combineRightR,
  -- * Lambda-abstraction
  abstractsR
) where

  import Prelude hiding (fail)

  import Mosquito.TermUtilities

  import Mosquito.Kernel.Term

  -- import Mosquito.Utility.Pretty    

  --
  -- * Derived rules
  --

  -- |Produces a derivation of @Gamma ⊢ t = t@ given @t@.
  reflexivityR :: Term -> Inference Theorem
  reflexivityR t = alphaR t t

  -- |Produces a derivation of @Gamma ⊢ f x = f y@ from a derivation of
  --  @Gamma ⊢ x = y@ provided the supplied term @f@ is of the correct type.
  combineRightR :: Term -> Theorem -> Inference Theorem
  combineRightR t thm = do
    eq <- reflexivityR t
    combineR eq thm

  -- |Produces a derivation of @Gamma ⊢ f x = g x@ from a derivation of
  --  @Gamma ⊢ f = g@ provided the supplied term @x@ is of the correct type.
  combineLeftR :: Term -> Theorem -> Inference Theorem
  combineLeftR t thm = do
    eq <- reflexivityR t
    combineR thm eq

  -- |Generalised for of "abstract", performing many abstractions one after
  --  the other.
  abstractsR :: [(String, Type)] -> Theorem -> Inference Theorem
  abstractsR xs thm =
    foldr (\(name, ty) prev -> do
      nPrev <- prev
      abstractR name ty nPrev) (return thm) xs

  proveHypothesisR :: Theorem -> Theorem -> Inference Theorem
  proveHypothesisR left right =
    if conclusion left `elem` hypotheses right then do
      das <- deductAntiSymmetricR left right
      equalityModusPonensR das left
    else
      return right