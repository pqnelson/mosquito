{-# LANGUAGE ViewPatterns #-}

-- |Derived, useful theorems --- direct consequences of the primitive inference
--  rules defined in the kernel.
module Mosquito.DerivedRules (
  -- * Reflexivity
  reflexivity,
  -- * Restricted combination rules
  combineL, combineR,
  -- * Lambda-abstraction
  abstracts,
  -- * Reductions
  betas
) where

  import Prelude hiding (fail)

  import Mosquito.TermUtilities

  import Mosquito.Kernel.Term

  -- import Mosquito.Utility.Pretty    

  --
  -- * Derived rules
  --

  -- |Produces a derivation of @Gamma ⊢ t = t@ given @t@.
  reflexivity :: Term -> Inference Theorem
  reflexivity t = alpha t t

  -- |Produces a derivation of @Gamma ⊢ f x = f y@ from a derivation of
  --  @Gamma ⊢ x = y@ provided the supplied term @f@ is of the correct type.
  combineL :: Term -> Theorem -> Inference Theorem
  combineL t thm = do
    eq <- reflexivity t
    combine eq thm

  -- |Produces a derivation of @Gamma ⊢ f x = g x@ from a derivation of
  --  @Gamma ⊢ f = g@ provided the supplied term @x@ is of the correct type.
  combineR :: Term -> Theorem -> Inference Theorem
  combineR t thm = do
    eq <- reflexivity t
    combine thm eq

  -- |Generalised for of "abstract", performing many abstractions one after
  --  the other.
  abstracts :: [(String, Type)] -> Theorem -> Inference Theorem
  abstracts xs thm =
    foldr (\(name, ty) prev -> do
      nPrev <- prev
      abstract name ty nPrev) (return thm) xs

  betas :: Term -> Inference Theorem
  betas = go . unfoldAppsL
    where
      go :: [Term] -> Inference Theorem
      go []         = fail "`betas'"
      go [x]        = reflexivity x
      go (x:xs:xss) = do
        app        <- mkApp x xs
        b          <- beta app
        (_, r)     <- fromEquality . conclusion $ b
        tl         <- go $ r:xss
        transitivity b tl