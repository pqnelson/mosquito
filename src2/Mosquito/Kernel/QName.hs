{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Mosquito.Kernel.QName where

  import Data.Monoid

  import Mosquito.Kernel.Dependent.Nat
  import Mosquito.Kernel.Dependent.Vector
  
  import Mosquito.Utility.Pretty
  
  data QName a m where
    QName :: Vector a m -> a -> QName a m
    
  deriving instance Eq a => Eq (QName a m)
  deriving instance Ord a => Ord (QName a m)
  deriving instance Show a => Show (QName a m)
    
  mkQName :: Vector a (S m) -> a -> QName a (S m)
  mkQName = QName  
    
  path :: QName a m -> Vector a m
  path (QName path head) = path
  
  head :: QName a m -> a
  head (QName path head) = head
  
  getPathComponent :: NatS n -> n :<: m -> QName a m -> a
  getPathComponent n prf (QName path head) = index n prf path
  
  instance Pretty a => Pretty (QName a m) where
    pretty (QName Nil  head) = pretty head
    pretty (QName path head) = mconcat [ppath path, ".", pretty head]
      where
        ppath :: Pretty a => Vector a m -> String
        ppath Nil        = ""
        ppath (x :# Nil) = pretty x
        ppath (x :# xs)  = mconcat [pretty x, ".", ppath xs]
