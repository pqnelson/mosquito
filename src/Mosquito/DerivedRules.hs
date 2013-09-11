-- |Derived, useful theorems --- direct consequences of the primitive inference
--  rules defined in the kernel.
module Mosquito.DerivedRules (
  -- * Reflexivity
  reflexivity,
  -- * Restricted combination rules
  combineL, combineR,
  -- * Lambda-abstraction
  abstracts
) where

  import Prelude hiding (fail)

  import Control.Monad hiding (fail)

  import qualified Data.Set as S

  import Mosquito.Kernel.QualifiedName
  import Mosquito.Kernel.Term

  --
  -- * Derived rules
  --

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

  -- |Produces a derivation of @Gamma ⊢ λx1:ty1 ... λxn:tyn. t = λy1:ty'1 ... λyn:ty'n. u@
  --  from a derivation of @Gamma ⊢ t = u@.
  abstracts :: [(String, Type)] -> Theorem -> Inference Theorem
  abstracts xs thm =
    foldr (\(name, ty) -> (>> abstract name ty thm)) (return thm) xs