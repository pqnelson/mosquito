{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Mosquito.Kernel.Dependent.Nat where

  import qualified Prelude

  import Mosquito.Utility.Pretty

  import Data.Monoid

  data Nat where
    Z :: Nat
    S :: Nat -> Nat
    deriving(Prelude.Eq, Prelude.Show, Prelude.Ord)
    
  data NatS (m :: Nat) where
    ZS :: NatS Z
    SS :: NatS m -> NatS (S m)
  
  deriving instance Prelude.Eq (NatS m)
  deriving instance Prelude.Show (NatS m)
  deriving instance Prelude.Ord (NatS m)
  
  type One = S Z
  
  --
  -- Misc
  --
  
  toInteger :: Nat -> Prelude.Integer
  toInteger Z     = 0
  toInteger (S m) = (Prelude.+) 1 (toInteger m)
  
  fromInteger :: Prelude.Integer -> Nat
  fromInteger 0 = Z
  fromInteger m
    | (Prelude.<) m 0   = Prelude.error "fromInteger: negative integer"
    | Prelude.otherwise = S (fromInteger ((Prelude.-) m 1))
  
  --
  -- Pred
  --
  
  pred :: Nat -> Nat
  pred Z     = Z
  pred (S m) = m
  
  type family Pred (m :: Nat) :: Nat where
    Pred Z     = Z
    Pred (S m) = m
  
  --
  -- Addition
  --
  
  (+) :: Nat -> Nat -> Nat
  Z   + n = n
  S m + n = S (m + n)
  
  type family (:+:) (m :: Nat) (n :: Nat) :: Nat where
    Z   :+: n = n
    S m :+: n = S (m :+: n)
  
  
  --
  -- Multiplication
  --
  
  (*) :: Nat -> Nat -> Nat
  Z   * n = Z
  S m * n = (m * n) + n
    
  type family (:*:) (m :: Nat) (n :: Nat) :: Nat where
    Z   :*: n = Z
    S m :*: n = (m :*: n) :+: n
    
  --
  -- Orderings
  --
  
  data (:<=:) (m :: Nat) (n :: Nat) where
    LEBase :: forall n. Z :<=: n
    LEStep :: forall m n. m :<=: n -> S m :<=: S n
    
  type (:>=:) m n = n :<=: m
  
  type (:<:) m n = S m :<=: n
  
  type (:>:) m n = n :<: m
  
  --
  -- Maximum
  --
  
  type family Max (m :: Nat) (n :: Nat) :: Nat where
    Max Z     m     = m
    Max n     Z     = n
    Max (S m) (S n) = S (Max m n)
  
  --
  -- Instances
  --
  
  instance Pretty Nat where
    pretty i = Prelude.show (toInteger i)
