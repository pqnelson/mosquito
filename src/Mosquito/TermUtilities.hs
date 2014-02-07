{-# LANGUAGE ViewPatterns #-}

-- |Provides some utilities for working with data types provided
--  in the kernel that can safely be moved outside of the kernel.
module Mosquito.TermUtilities (
  -- * Utility functions
  partialFromSuccess, freshs,
  -- * Useful deconstruction functions
  fromBinaryOperation,
  -- * Useful construction funtions
  mkVars, mkLams,
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

  -- |Generates a list of fresh names of a given length, using a suggested base
  --  name (otherwise defaulting to "f" as the base) and avoiding any names
  --  present in the provided set of names.
  freshs :: Int -> Maybe String -> S.Set String -> [String]
  freshs 0 base seen = []
  freshs n base seen =
    let name   = fresh base seen in
    let others = freshs (n - 1) base (S.insert name seen) in
      name:others

  --
  -- * More useful construction functions
  --

  -- |Generalised form of "mkVar".  Creates a list of variables based
  --  on a given association list between names of variables and types.
  mkVars :: [(String, Type)] -> Inference [Term]
  mkVars []              = fail "mkVars: input list empty"
  mkVars [(name, ty)]    = return . return $ mkVar name ty
  mkVars ((name, ty):xs) = do
    tail     <- mkVars xs
    let head =  mkVar name ty
    return (head:tail)

  -- |Generalised form of "mkLam".  Creates an n-fold lambda-abstraction over
  --  a given term based on a given association list of names of variables to
  --  abstract and their types.
  mkLams :: [(String, Type)] -> Term -> Term
  mkLams []           body = body
  mkLams ((n, ty):xs) body = mkLam n ty (mkLams xs body)

  --
  -- * More useful deconstruction functions
  --

  -- |Deconstructs an arbitrary binary operation.  The operation
  --  is the first element return, the left and right arguments of the
  --  operation follow.
  fromBinaryOperation :: Term -> Inference (Term, Term, Term)
  fromBinaryOperation term = do
    (app, right) <- fromApp term
    (op, left)   <- fromApp app
    return (op, left, right)

  --
  -- * Type utilities
  --

  -- |Unifies two types.
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