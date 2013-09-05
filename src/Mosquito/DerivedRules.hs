module Mosquito.DerivedRules where

  import Prelude hiding (fail)
  import Control.Monad hiding (fail)

  import Mosquito.Kernel.QualifiedName
  import Mosquito.Kernel.Term

  --
  -- * Some utilities
  --

  constantOfDecl :: Inference (Term, a) -> Inference Term
  constantOfDecl decl = decl >>= \decl -> return . fst $ decl

  theoremOfDecl :: Inference (a, Theorem) -> Inference Theorem
  theoremOfDecl decl = decl >>= \decl -> return . snd $ decl

  --
  -- * True derived rules that belong here...
  --

  simpleReflexivity :: Term -> Inference Theorem
  simpleReflexivity t = reflexivity t t 

  -- |Produces a derivation of @Gamma ⊢ f x = f y@ from a derivation of
  --  @Gamma ⊢ x = y@ provided the supplied term @f@ is of the correct type.
  combineL :: Term -> Theorem -> Inference Theorem
  combineL t thm = do
    eq <- simpleReflexivity t
    combine eq thm

  -- |Produces a derivation of @Gamma ⊢ f x = g x@ from a derivation of
  --  @Gamma ⊢ f = g@ provided the supplied term @x@ is of the correct type.
  combineR :: Term -> Theorem -> Inference Theorem
  combineR t thm = do 
    eq <- simpleReflexivity t
    combine thm eq
    
  abstracts :: [(String, Type)] -> Theorem -> Inference Theorem
  abstracts []              thm = return thm
  abstracts ((name, ty):xs) thm = abstract name ty thm >> abstracts xs thm