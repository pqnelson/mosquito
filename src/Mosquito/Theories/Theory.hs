{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Mosquito.Theories.Theory
where

  import Data.Label
  import qualified Data.Map as M
  import qualified Data.Set as S

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.Utility.Pretty

  data Theory
    = Theory {
      _name      :: QualifiedName
    , _parents   :: S.Set Theory
    , _theorems  :: M.Map QualifiedName Theorem
    , _constants :: S.Set ConstantDescription
    , _typeOps   :: S.Set TypeOperatorDescription
    } deriving (Eq, Ord)

  mkLabels [''Theory]

  primitiveHOL :: Theory
  primitiveHOL =
    Theory {
      _name      = mkQualifiedName ["Mosquito"] "Primitive"
    , _parents   = S.empty
    , _theorems  = M.empty
    , _constants = S.singleton equalityDescription
    , _typeOps   = S.fromList [functionDescription, boolDescription]
    }

  getName :: Theory -> QualifiedName
  getName = get name

  getParents :: Theory -> S.Set Theory
  getParents = get parents

  getParentsQualifiedNames :: Theory -> S.Set QualifiedName
  getParentsQualifiedNames = S.map (get name) . get parents

  getTheorem :: Theory -> QualifiedName -> Either String Theorem
  getTheorem thy nm =
      case M.lookup name' $ get theorems thy of
        Nothing ->
          Left . unwords $ [
            "getTheorem: no theorem of name `", pretty name', "' in theory"
          ]
        Just thm -> return thm
    where
      name' :: QualifiedName
      name' =
        if null $ qualifiedNamePath nm then
          let theoryName = get name thy in
          let path = qualifiedNamePath theoryName ++ [qualifiedNameHead theoryName] in
            mkQualifiedName path $ qualifiedNameHead nm
        else
          nm
