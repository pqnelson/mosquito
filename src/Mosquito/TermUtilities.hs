-- |Provides some utilities for working with data types provided
--  in the kernel that can safely be moved outside of the kernel.
module Mosquito.TermUtilities (
  -- * Unfolding applications
  unfoldAppsL, unfoldAppsR
)
where

  import Mosquito.Kernel.Term

  --
  -- * Unfolding applications
  --

  -- |Unfolds a left associatied series of applications of
  --  the form @(((t t') t'') t''') ...@.
  unfoldAppsL :: Term -> [Term]
  unfoldAppsL trm =
    case fromApp trm of
      Fail{} -> []
      Success (l, r) -> unfoldAppsL l ++ [r]

  -- |Unfolds a right associated series of applications of
  --  the form @t (t' (t'' (t''' ...)))@.
  unfoldAppsR :: Term -> [Term]
  unfoldAppsR trm =
    case fromApp trm of
      Fail{} -> []
      Success (l, r) -> l:unfoldAppsR r