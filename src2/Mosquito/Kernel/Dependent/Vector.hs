{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Mosquito.Kernel.Dependent.Vector where

  import qualified Prelude
  
  import Mosquito.Kernel.Dependent.Nat
  
  data Vector :: * -> Nat -> * where
    Nil  :: Vector a Z
    (:#) :: a -> Vector a m -> Vector a (S m)
    
  deriving instance Prelude.Eq a => Prelude.Eq (Vector a m)
  deriving instance Prelude.Ord a => Prelude.Ord (Vector a m)
  deriving instance Prelude.Show a => Prelude.Show (Vector a m)
    
  nil :: Vector a Z
  nil = Nil
  
  cons :: a -> Vector a m -> Vector a (S m)
  cons = (:#)
  
  singleton :: a -> Vector a One
  singleton x = x :# Nil
  
  map :: (a -> b) -> Vector a m -> Vector b m
  map f Nil       = Nil
  map f (x :# xs) = f x :# map f xs
  
  (++) :: Vector a m -> Vector a n -> Vector a (m :+: n)
  Nil       ++ ys = ys
  (x :# xs) ++ ys = x :# (xs ++ ys)
  
  index :: NatS m -> m :<: n -> Vector a n -> a
  index ZS     _            (x :# xs) = x
  index (SS m) (LEStep prf) (x :# xs) = index m prf xs
  
