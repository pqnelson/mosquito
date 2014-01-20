{-# LANGUAGE ViewPatterns #-}

-- |Provides some utilities for working with data types provided
--  in the kernel that can safely be moved outside of the kernel.
module Mosquito.TermUtilities (
  -- * Utility functions
  partialFromSuccess,
  -- * Type utilities
  unifyTypes
)
where

  import Prelude hiding (fail)

  import qualified Data.Set as S

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  --
  -- * Utility functions
  --

  -- |Partial function extracting the result of a successful computation in
  --  the "Inference" monad, throwing an exception if the computation had
  --  not been successful.
  partialFromSuccess :: Inference a -> a
  partialFromSuccess inf =
    inference inf
      (const . error $ "partialFromSuccess")
      id

  --
  -- * Type utilities
  --

  unifyTypes :: Type -> Type -> Inference (Substitution Type)
  unifyTypes (typeView->TyVarView t)            right@(typeView->TyVarView t')
    | t == t'   = return empty
    | otherwise = return . mkSubstitution $ [(t, right)]
  unifyTypes (typeView->TyVarView t)            right
    | t `S.member` tv right =
        fail . unwords $ [
          unwords ["unifyTypes: occurs check failure.  Type variable `", t, "' occurs"]
        , unwords ["in type `", pretty right, "'."]
        ]
    | otherwise             = return . mkSubstitution $ [(t, right)]
  unifyTypes left                               (typeView->TyVarView t)
    | t `S.member` tv left =
        fail . unwords $ [
          unwords ["unifyTypes: occurs check failure.  Type variable `", t, "' occurs"]
        , unwords ["in type `", pretty left, "'."]
        ]
    | otherwise = return . mkSubstitution $ [(t, left)]
  unifyTypes (typeView->TyOperatorView op args) (typeView->TyOperatorView op' args')
    | op == op' = do
        args <- mapM (uncurry unifyTypes) $ zip args args'
        return $ foldr compose empty args
    | otherwise =
        fail . unwords $ [
          unwords ["unifyTypes: cannot unify type operator `", pretty op, "' with"]
        , unwords ["type operator `", pretty op', "'.  Type operators must be identical"]
        , "to be unifiable."
        ]