-- |Provides some utilities for working with data types provided
--  in the kernel that can safely be moved outside of the kernel.
module Mosquito.TermUtilities (
  -- * Unfolding applications
  unfoldAppsL, unfoldAppsR
)
where

  import Mosquito.Kernel.Term

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
  -- ** Unfolding applications
  --

  -- |Unfolds a left associatied series of applications of
  --  the form @(((t t') t'') t''') ...@.
  unfoldAppsL :: Term -> [Term]
  unfoldAppsL trm =
    inference (fromApp trm)
      (const [])
      (\(l, r) -> unfoldAppsL l ++ [r])

  -- |Unfolds a right associated series of applications of
  --  the form @t (t' (t'' (t''' ...)))@.
  unfoldAppsR :: Term -> [Term]
  unfoldAppsR trm =
    inference (fromApp trm)
      (const [])
      (\(l, r) -> l : unfoldAppsR r)

  --
  -- * Views
  --

  --
  -- ** Type views
  --

  -- |This is a view for types that allows you to pattern match on types outside
  --  of the kernel using GHC's ViewPattern extension.  A type is either a
  --  type variable or a type operator, as in the kernel.
  data TypeView
    = TyVar String
    | TyOperator TypeOperatorDescription [Type]

  -- |The transformation from "Type" to its view, "TypView".
  --  NOTA BENE: this function is (potentially) partial as it relies on
  --  "partialFromSuccess".  This partiality should never appear as long
  --  as "fromTyVar" returns "Success v" for some "v" whenever "isTyVar"
  --  returns "True" and "isTyVar ty && isTyOperator ty" always returns
  --  "True" (i.e. there are no more syntactic classes of types than
  --  type variables and type operators).
  typView :: Type -> TypeView
  typView typ =
    if isTyVar typ then
      TyVar . partialFromSuccess . fromTyVar $ typ
    else
      uncurry TyOperator . partialFromSuccess . fromTyOperator $ typ

  -- |This is a custom view for function types.  A type under this view is either
  --  a function type, in which case we place the domain and range types of that
  --  function into a constructor "Function", otherwise it is not.  Again, this is
  --  fully exposed outside of the kernel so that we can do some neat pattern
  --  matching without sacrificing abstraction.
  data FunView
    = Function     Type Type
    | NotAFunction Type

  -- |The transformation from "Type" to its custom view, "FunctionView".
  --  NOTA BENE: this function is (potentially) partial as it relies on
  --  "partialFromSuccess".  This partiality should never appear as long
  --  as "fromFunction" returns "Success (dom, rng)" for some "dom" and
  --  "rng" whenever "isFunction" returns "True".
  funView :: Type -> FunView
  funView typ =
    if isFunction typ then
      uncurry Function . partialFromSuccess . fromFunction $ typ
    else
      NotAFunction typ

  --
  -- ** Term views
  --

  -- |A view type for "Term", allowing users outside of the kernel to
  --  pattern match on "Term" without sacrificing abstraction of the "Term"
  --  data type.
  data TermView
    = Var   String Type
    | Const ConstantDescription
    | App   Term Term
    | Lam   String Type Term


  -- |Transformation between "Term" and "TermView".
  termView :: Term -> TermView
  termView t =
      if isVar t then
        uncurry Var . partialFromSuccess . fromVar $ t
      else if isConst t then
        Const . partialFromSuccess . fromConst $ t
      else if isApp t then
        uncurry App . partialFromSuccess . fromApp $ t
      else
        uncurry3 Lam . partialFromSuccess . fromLam $ t
    where
      uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
      uncurry3 f (x, y, z) = f x y z

  -- |View type for equality.  A term is either an equality in this scheme, in
  --  which case "Equality" holds the left and right hand sides of the equality
  --  or it is something else, in which case "NotEquality" is returned.
  data EqView
    = Equality      Term Term
    | NotAnEquality Term

  eqView :: Term -> EqView
  eqView t =
    if isEquality t then
      uncurry Equality . partialFromSuccess . fromEquality $ t
    else
      NotAnEquality t