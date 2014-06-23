{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Mosquito.Kernel.Kernel where

  import Mosquito.Kernel.Dependent.Nat

  data Type where
    Prop :: Type

  data Term :: * -> Nat -> Type -> * where
    Dummy :: Term a m phi
  
  mkEquality :: Term a m phi -> Term a m Prop
  mkEquality = undefined
