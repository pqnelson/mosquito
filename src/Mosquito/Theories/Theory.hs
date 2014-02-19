{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Mosquito.Theories.Theory (
  PrettyPrintingEntry(..),
  Theory, newTheory,
  primitiveHOL,
  getName, getParents, getParentsQualifiedNames,
  getTheorem, getTheoremCurrent,
  getConstantDescription, getConstantDescriptionCurrent,
  getConstant, getConstantCurrent,
  getTypeOperatorDescription, getTypeOperatorDescriptionCurrent,
  registerTheorem, registerConstantDescription, registerTypeOperatorDescription,
  registerNewDefinition, registerNewAxiom, registerNewType,
  registerNewLatexRepresentation, registerNewLatexRepresentationCurrent,
  registerNewUnicodeRepresentation, registerNewUnicodeRepresentationCurrent
)
where

  import Prelude hiding (fail)

  import Data.Label
  import qualified Data.List as L
  import qualified Data.Map as M
  import qualified Data.Set as S

  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName

  import Mosquito.Utility.Pretty

  data PrettyPrintingEntry
    = NoFix   String
    | Postfix String
    | Infix   String
    | Mixfix  [String]
      deriving (Eq, Ord)

  type IsBinder = Bool

  data Theory
    = Theory {
      _name      :: QualifiedName
    , _parents   :: S.Set Theory
    , _theorems  :: M.Map QualifiedName Theorem
    , _constants :: M.Map QualifiedName ConstantDescription
    , _typeOps   :: M.Map QualifiedName TypeOperatorDescription
    , _latex     :: M.Map QualifiedName (PrettyPrintingEntry, IsBinder)
    , _unicode   :: M.Map QualifiedName (PrettyPrintingEntry, IsBinder)
    } deriving (Eq, Ord)

  mkLabels [''Theory]

  instance Pretty Theory where
    pretty thy =
      L.intercalate "\n" [
        unwords $ ["theory", pretty (get name thy), "extending"] ++ (L.map (pretty . get name) $ S.toAscList $ get parents thy)
      , "THEOREMS:"
      , "  " ++ (L.intercalate "\n  " $ L.map (\(n, t) -> pretty n ++ ": " ++ pretty t) $ M.toAscList $ get theorems thy)
      , "CONSTANT DESCRIPTIONS"
      , "  " ++  (L.intercalate "\n  " $ L.map (\(n, t) -> pretty n) $ M.toAscList $ get constants thy)
      , "TYPE OPERTOR DESCRIPTIONS"
      , "  " ++  (L.intercalate "\n  " $ L.map (\(n, t) -> pretty n) $ M.toAscList $ get typeOps thy)
      ]

  primitiveHOL :: Theory
  primitiveHOL =
    Theory {
      _name      = mkQualifiedName ["Mosquito"] "Primitive"
    , _parents   = S.empty
    , _theorems  = M.empty
    , _constants =
        M.fromList [
          (mkQualifiedName ["Mosquito", "Primitive"] "equality", equalityDescription)
        ]
    , _typeOps   =
        M.fromList [
          (mkQualifiedName ["Mosquito", "Primitive"] "Arrow", functionDescription)
        , (mkQualifiedName ["Mosquito", "Primitive"] "Bool", boolDescription)
        ]
    , _latex     =
        M.fromList [
          (mkQualifiedName ["Mosquito", "Primitive"] "Arrow", (Infix "\\Rightarrow", False))
        , (mkQualifiedName ["Mosquito", "Primitive"] "equality", (Infix "=", False))
        ]
    , _unicode   =
        M.fromList [
          (mkQualifiedName ["Mosquito", "Primitive"] "Arrow", (Infix "⇒", False))
        , (mkQualifiedName ["Mosquito", "Primitive"] "equality", (Infix "=", False))
        ]
    }

  newTheory :: [Theory] -> QualifiedName -> Theory
  newTheory parents name =
    Theory {
      _name      = name
    , _parents   = S.fromList parents
    , _theorems  = M.unions $ map (get theorems) parents
    , _constants = M.unions $ map (get constants) parents
    , _typeOps   = M.unions $ map (get typeOps) parents
    , _latex     = M.unions $ map (get latex) parents
    , _unicode   = M.unions $ map (get unicode) parents
    }

  isRegisteredName :: Theory -> QualifiedName -> Bool
  isRegisteredName thy name =
    L.elem name $ concat [
      M.keys $ get theorems thy
    , M.keys $ get constants thy
    , M.keys $ get typeOps thy
    ]

  getName :: Theory -> QualifiedName
  getName = get name

  getParents :: Theory -> S.Set Theory
  getParents = get parents

  getParentsQualifiedNames :: Theory -> S.Set QualifiedName
  getParentsQualifiedNames = S.map (get name) . get parents

  getNameAsPath :: Theory -> [String]
  getNameAsPath thy =
    let name' = get name thy in
      qualifiedNamePath name' ++ [qualifiedNameHead name']

  genericGet :: (Theory -> M.Map QualifiedName a) -> Theory -> QualifiedName -> Inference a
  genericGet f thy nm =
      case M.lookup name' $ f thy of
        Nothing ->
          fail . unwords $ [
            "genericGet: no object of name `", pretty name', "' in theory."
          ]
        Just thm -> return thm
    where
      name' :: QualifiedName
      name' =
        if null $ qualifiedNamePath nm then
          mkQualifiedName (getNameAsPath thy) $ qualifiedNameHead nm
        else
          nm

  getTheorem :: Theory -> QualifiedName -> Inference Theorem
  getTheorem = genericGet $ get theorems

  getTheoremCurrent :: Theory -> String -> Inference Theorem
  getTheoremCurrent thy nm = do
    let name' = mkQualifiedName (getNameAsPath thy) nm
    getTheorem thy name'

  getConstantDescription :: Theory -> QualifiedName -> Inference ConstantDescription
  getConstantDescription = genericGet $ get constants

  getConstantDescriptionCurrent :: Theory -> String -> Inference ConstantDescription
  getConstantDescriptionCurrent thy nm = do
    let name' = mkQualifiedName (getNameAsPath thy) nm
    getConstantDescription thy name'

  getTypeOperatorDescription :: Theory -> QualifiedName -> Inference TypeOperatorDescription
  getTypeOperatorDescription = genericGet $ get typeOps

  getTypeOperatorDescriptionCurrent :: Theory -> String -> Inference TypeOperatorDescription
  getTypeOperatorDescriptionCurrent thy nm = do
    let name' = mkQualifiedName (getNameAsPath thy) nm
    getTypeOperatorDescription thy name'

  getConstant :: Theory -> QualifiedName -> Inference Term
  getConstant thy nm = do
    cd <- getConstantDescription thy nm
    return . mkConst $ cd

  getConstantCurrent :: Theory -> String -> Inference Term
  getConstantCurrent thy nm = do
    let name' = mkQualifiedName (getNameAsPath thy) nm
    getConstant thy name'

  registerTheorem :: Theory -> String -> Theorem -> Inference Theory
  registerTheorem thy nm thm =
    let name' = mkQualifiedName (getNameAsPath thy) nm in
      if M.member name' $ get theorems thy then
        fail . unwords $ [
          "registerTheorem: theorem `", pretty name', "' is already registered in theory."
        ]
      else
        return $ modify theorems (M.insert name' thm) thy

  registerConstantDescription :: Theory -> String -> ConstantDescription -> Inference Theory
  registerConstantDescription thy nm cd =
    let name' = mkQualifiedName (getNameAsPath thy) nm in
      if M.member name' $ get constants thy then
        fail . unwords $ [
          "registerConstantDescription: constant descripton `", pretty name', "' is already registered in theory."
        ]
      else
        return $ modify constants (M.insert name' cd) thy

  registerTypeOperatorDescription :: Theory -> String -> TypeOperatorDescription -> Inference Theory
  registerTypeOperatorDescription thy nm td =
    let name' = mkQualifiedName (getNameAsPath thy) nm in
      if M.member name' $ get constants thy then
        fail . unwords $ [
          "registerTypeOperatorDescription: type operator descripton `", pretty name', "' is already registered in theory."
        ]
      else
        return $ modify typeOps (M.insert name' td) thy

  registerNewDefinition :: Theory -> String -> Term -> Type -> Inference Theory
  registerNewDefinition thy nm defn typ = do
    let name' = mkQualifiedName (getNameAsPath thy) nm
    (cnst, thm) <- primitiveNewDefinedConstant name' defn typ
    cd  <- fromConst cnst
    thy <- registerConstantDescription thy nm cd
    registerTheorem thy (nm ++ "D") thm

  registerNewAxiom :: Theory -> String -> Term -> Inference Theory
  registerNewAxiom thy nm axiom = do
    thm <- primitiveNewAxiom axiom
    registerTheorem thy nm thm

  registerNewType :: Theory -> String -> Theorem -> Inference Theory
  registerNewType thy nm inhab = do
    let name' = mkQualifiedName (getNameAsPath thy) nm
    let absN  = nm ++ "Abs"
    let repN  = nm ++ "Rep"
    let inN   = nm ++ "In"
    let outN  = nm ++ "Out"
    (in', out, abs, rep, td) <- primitiveNewDefinedType name' inhab
    absC      <- fromConst abs
    repC      <- fromConst rep
    thy       <- registerTheorem thy inN in'
    thy       <- registerTheorem thy outN out
    thy       <- registerConstantDescription thy absN absC
    thy       <- registerConstantDescription thy repN repC
    registerTypeOperatorDescription thy nm td

  registerNewLatexRepresentation :: Theory -> QualifiedName -> (PrettyPrintingEntry, IsBinder) -> Inference Theory
  registerNewLatexRepresentation thy name entry =
    if isRegisteredName thy name then
      return $ modify latex (M.insert name entry) thy
    else
      fail . unwords $ [
        "registerNewLatexRepresentation: cannot register pretty-printing entry for `", pretty name, "'"
      , "as the name is not associated to any theorem, constant or type operator description in the"
      , "theory."
      ]

  registerNewLatexRepresentationCurrent :: Theory -> String -> (PrettyPrintingEntry, IsBinder) -> Inference Theory
  registerNewLatexRepresentationCurrent thy name entry =
    let name' = mkQualifiedName (getNameAsPath thy) name in
      registerNewLatexRepresentation thy name' entry

  registerNewUnicodeRepresentation :: Theory -> QualifiedName -> (PrettyPrintingEntry, IsBinder) -> Inference Theory
  registerNewUnicodeRepresentation thy name entry =
    if isRegisteredName thy name then
      return $ modify unicode (M.insert name entry) thy
    else
      fail . unwords $ [
        "registerNewUnicodeRepresentation: cannot register pretty-printing entry for `", pretty name, "'"
      , "as the name is not associated to any theorem, constant or type operator description in the"
      , "theory."
      ]

  registerNewUnicodeRepresentationCurrent :: Theory -> String -> (PrettyPrintingEntry, IsBinder) -> Inference Theory
  registerNewUnicodeRepresentationCurrent thy name entry =
    let name' = mkQualifiedName (getNameAsPath thy) name in
      registerNewUnicodeRepresentation thy name' entry
