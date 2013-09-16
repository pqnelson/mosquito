{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Mosquito.Theories.Theory {- (
  -- * Theories and miscellaneous utility functions
  Theory,
  isDeclaredTheoremOrAxiom, isDeclaredConstant, isDeclaredTypeFormer,
  declaredAxiomQualifiedNames, declaredTheoremQualifiedNames, declaredTypeFormerQualifiedNames,
  declaredAxioms, declaredTheorems,
  getTheorem,
  -- * Base theories and creating new theories
  caracal, mkTheory,
  -- * Extending an existing theory
  newAxiom, newDefinedConstant, newTheorem
) -}
where

  import Prelude hiding (fail)

  import Data.Label
  import qualified Data.List as L
  import qualified Data.Set as S

  import qualified Mosquito.Kernel.Term as K
  import Mosquito.Kernel.QualifiedName

  import Mosquito.Utility.Pretty

  --
  -- * Theories and miscellaneous utility functions
  --

  data TheoremType
    = Axiomatised
    | Proved
    deriving(Eq, Show, Ord)

  data Theory = Theory {
    _name      :: QualifiedName,
    _constants :: S.Set QualifiedName,
    _theorems  :: S.Set (TheoremType, QualifiedName),
    _types     :: S.Set QualifiedName
  } deriving(Eq, Show, Ord)

  mkLabels [''Theory]

  qualifiedNameInTheory :: Theory -> [String]
  qualifiedNameInTheory theory = 
    (qualifiedNamePath . get name $ theory) ++ [qualifiedNameHead . get name $ theory]

  theoryQualifiedName :: Theory -> QualifiedName
  theoryQualifiedName = get name

  isDeclaredTheoremOrAxiom :: QualifiedName -> Theory -> Bool
  isDeclaredTheoremOrAxiom nm theory = S.member nm . S.map snd $ get theorems theory

  isDeclaredConstant :: QualifiedName -> Theory -> Bool
  isDeclaredConstant nm theory = S.member nm $ get constants theory

  isDeclaredTypeFormer :: QualifiedName -> Theory -> Bool
  isDeclaredTypeFormer nm = S.member nm . get types

  declaredAxiomQualifiedNames :: Theory -> S.Set QualifiedName
  declaredAxiomQualifiedNames =
    S.map snd . S.filter (\x -> fst x == Axiomatised) . get theorems

  declaredTheoremQualifiedNames :: Theory -> S.Set QualifiedName
  declaredTheoremQualifiedNames =
    S.map snd . S.filter (\x -> fst x == Proved) . get theorems

  declaredTypeFormerQualifiedNames :: Theory -> S.Set QualifiedName
  declaredTypeFormerQualifiedNames = get types

  --
  -- * Base theories and functions for creating new theories
  --

  -- |Base theory of the Mosquito logic, containing the names of
  --  native constants (e.g. equality) and type names such as
  --  the function space and the booleans.
  caracal :: Theory
  caracal =
    Theory {
      _name      = mkQualifiedName ["Mosquito"] "Mosquito",
      _constants = S.singleton K.equalityQualifiedName,
      _theorems  = S.empty,
      _types     = S.fromList [K.boolQualifiedName, K.functionQualifiedName]
    }

  -- |Create a new theory.  All theories barring the base Mosquito
  --  theory are derived from some supertheory, with the derived
  --  subtheory inheriting all of the declared constants, theorems,
  --  axioms and so on of the supertheory.
  --  XXX: check for a sensible name (what is a sensible name?)
  mkTheory :: Theory -> String -> Theory
  mkTheory parent nm =
    Theory {
      _name      = mkQualifiedName ["Mosquito"] nm,
      _constants = get constants parent,
      _theorems  = get theorems parent,
      _types     = get types parent
    }

  --
  -- * Extending an existing theory
  --

  newAxiom :: Theory -> String -> K.Term -> K.Inference (K.Theorem, Theory)
  newAxiom theory ident axiom =
    let path  = qualifiedNameInTheory theory in
    let qname = mkQualifiedName path ident in
      if isDeclaredTheoremOrAxiom qname theory then
        K.fail $ "Axiom `" ++ pretty qname ++ "' already declared in theory `" ++ pretty (get name theory) ++ "'."
      else do
        axiomatised <- K.primitiveNewAxiom axiom
        let newTheory   =  modify theorems (S.insert (Axiomatised, qname)) theory
        return (axiomatised, newTheory)

  newTheorem :: Theory -> String -> K.Inference Theory
  newTheorem theory ident =
    let path  = qualifiedNameInTheory theory in
    let qname = mkQualifiedName path ident in
      if isDeclaredTheoremOrAxiom qname theory then
        K.fail $ "Theorem `" ++ pretty qname ++ "' already declared in theory `" ++ pretty (get name theory) ++ "'."
      else
        return $ modify theorems (S.insert (Proved, qname)) theory

  newDefinedConstant :: Theory -> String -> K.Term -> K.Type -> K.Inference (K.Term, K.Theorem, Theory)
  newDefinedConstant theory ident def typ =
    let path    = qualifiedNameInTheory theory in
    let qname   = mkQualifiedName path ident in
    let defName = mkQualifiedName path $ ident ++ "D" in
      if isDeclaredConstant qname theory then
        K.fail $ "Constant `" ++ pretty qname ++ "' already declared in theory `" ++ pretty (get name theory) ++ "'."
      else if isDeclaredTheoremOrAxiom defName theory then
        K.fail $ "Theorem `" ++ pretty defName ++ "' already declared in theory `" ++ pretty (get name theory) ++ "'."
      else do
        (c, thm) <- K.primitiveNewDefinedConstant qname def typ
        let modified  = modify theorems (S.insert (Proved, defName)) theory
        return (c, thm, modify constants (S.insert qname) modified)
  --
  -- * Pretty printing theories
  --

  instance Pretty Theory where
    pretty theory =
        "Theory `" ++ (pretty $ get name theory) ++ "'." ++
        "\n  * Declared types:\n    " ++
        (L.intercalate "\n    " $ map pretty . S.toAscList $ get types theory) ++
        "\n  * Theorems:\n    " ++
        (L.intercalate "\n    " $ map prettyTheorem . S.toList $ get theorems theory) ++
        "\n  * Declared constants:\n    " ++
        (L.intercalate "\n    " $ map pretty . S.toList $ get constants theory)
      where
        prettyTheorem :: (TheoremType, QualifiedName) -> String
        prettyTheorem (t, qname) =
          case t of
            Axiomatised -> "[!] " ++ pretty qname
            Proved -> pretty qname