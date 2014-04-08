{-# LANGUAGE GADTs #-}

module Mosquito.Kernel.QualifiedName (
  NonEmpty,
  QualifiedName,
  mkQualifiedName
)
where

  import Control.Applicative

  import Data.NonEmpty

  type NonEmpty a = T [] a

  data QualifiedName where
    QualifiedName :: NonEmpty String -> String -> QualifiedName
    deriving(Eq, Ord, Show)

  mkQualifiedName :: NonEmpty String -> String -> QualifiedName
  mkQualifiedName = QualifiedName

  getPathOfQualifiedName :: QualifiedName -> NonEmpty String
  getPathOfQualifiedName (QualifiedName path head) = path

  getHeadOfQualifiedName :: QualifiedName -> String
  getHeadOfQualifiedName (QualifiedName path head) = head

  mapHead :: (String -> String) -> QualifiedName -> QualifiedName
  mapHead f (QualifiedName path head) = QualifiedName path $ f head

  mapPath :: (NonEmpty String -> NonEmpty String) -> QualifiedName -> QualifiedName
  mapPath f (QualifiedName path head) = QualifiedName (f path) head