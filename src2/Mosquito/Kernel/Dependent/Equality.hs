{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Mosquito.Kernel.Dependent.Equality where

  data (:==:) m n where
    Refl :: m ~ n => m :==: n
  
  --
  -- Equality is an equivalence
  --
    
  refl :: m ~ n => m :==: n
  refl = Refl
  
  sym :: m :==: n -> n :==: m
  sym Refl = Refl
  
  trans :: m :==: n -> n :==: o -> m :==: o
  trans Refl Refl = Refl
  
  --
  -- Equality really is equality
  --
  
  rewriteL :: m :==: n -> f m -> f n
  rewriteL Refl x = x
  
  rewriteR :: m :==: n -> f n -> f m
  rewriteR Refl x = x
  
  --
  -- Casting types
  -- 
  
  cast :: m :==: n -> m -> n
  cast Refl x = x
