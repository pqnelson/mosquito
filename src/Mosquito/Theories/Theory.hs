{-# LANGUAGE TemplateHaskell, TypeOperators, ViewPatterns #-}

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
  registerNewUnicodeRepresentation, registerNewUnicodeRepresentationCurrent,
  ShowTypes,
  unicodeTermInTheory, unicodeTypeInTheory, unicodeTheoremInTheory,
  latexTermInTheory, latexTypeInTheory, latexTheoremInTheory
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

  type IsBinder = Bool

  data PrettyPrintingEntry
    = NoFix   String IsBinder
    | Postfix String
    | Infix   String
      deriving (Eq, Ord)

  data Theory
    = Theory {
      _name      :: QualifiedName
    , _parents   :: S.Set Theory
    , _theorems  :: M.Map QualifiedName Theorem
    , _constants :: M.Map QualifiedName ConstantDescription
    , _typeOps   :: M.Map QualifiedName TypeOperatorDescription
    , _latex     :: M.Map QualifiedName PrettyPrintingEntry
    , _unicode   :: M.Map QualifiedName PrettyPrintingEntry
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
          (mkQualifiedName ["Mosquito", "Primitive"] "Arrow", Infix "\\rightarrow")
        , (mkQualifiedName ["Mosquito", "Primitive"] "equality", Infix "=")
        ]
    , _unicode   =
        M.fromList [
          (mkQualifiedName ["Mosquito", "Primitive"] "Arrow", Infix "→")
        , (mkQualifiedName ["Mosquito", "Primitive"] "equality", Infix "=")
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

  registerNewLatexRepresentation :: Theory -> QualifiedName -> PrettyPrintingEntry -> Inference Theory
  registerNewLatexRepresentation thy name entry =
    if isRegisteredName thy name then
      return $ modify latex (M.insert name entry) thy
    else
      fail . unwords $ [
        "registerNewLatexRepresentation: cannot register pretty-printing entry for `", pretty name, "'"
      , "as the name is not associated to any theorem, constant or type operator description in the"
      , "theory."
      ]

  registerNewLatexRepresentationCurrent :: Theory -> String -> PrettyPrintingEntry -> Inference Theory
  registerNewLatexRepresentationCurrent thy name entry =
    let name' = mkQualifiedName (getNameAsPath thy) name in
      registerNewLatexRepresentation thy name' entry

  registerNewUnicodeRepresentation :: Theory -> QualifiedName -> PrettyPrintingEntry -> Inference Theory
  registerNewUnicodeRepresentation thy name entry =
    if isRegisteredName thy name then
      return $ modify unicode (M.insert name entry) thy
    else
      fail . unwords $ [
        "registerNewUnicodeRepresentation: cannot register pretty-printing entry for `", pretty name, "'"
      , "as the name is not associated to any theorem, constant or type operator description in the"
      , "theory."
      ]

  registerNewUnicodeRepresentationCurrent :: Theory -> String -> PrettyPrintingEntry -> Inference Theory
  registerNewUnicodeRepresentationCurrent thy name entry =
    let name' = mkQualifiedName (getNameAsPath thy) name in
      registerNewUnicodeRepresentation thy name' entry

  --
  -- XXX: below should be moved elsewhere and not litter this file.
  --

  type ShowTypes = Bool

  unicodeTermInTheory :: Theory -> ShowTypes -> Term -> String
  unicodeTermInTheory thy showTypes = go
    where

      bracket :: Term -> String
      bracket trm =
        if size trm > 1 then
          "(" ++ go trm ++ ")"
        else
          go trm

      go :: Term -> String
      go (termView->AppView left right) =
        case termView left of
          AppView left' right' ->
            case termView left' of
              ConstView c ->
                let name = constantDescriptionQualifiedName c in
                let unic = get unicode thy in
                  case M.lookup name unic of
                    Nothing -> unwords [bracket left, bracket right]
                    Just en ->
                      case en of
                        NoFix sym binder ->
                          if binder then
                            case termView right' of
                              LamView name ty body ->
                                if showTypes then
                                  let ty' = unicodeTypeInTheory thy ty in
                                    sym ++ "(" ++ name ++ " : " ++ ty' ++ "). " ++ bracket body ++ bracket right
                                else
                                  sym ++ name ++ ". " ++ bracket body ++ bracket right
                              _                    -> unwords [sym, bracket right', bracket right]
                          else
                            unwords [sym, bracket right', bracket right]
                        Postfix sym         -> unwords [bracket left, bracket right, sym]
                        Infix sym           -> unwords [bracket right', sym, bracket right]
              _              -> unwords [bracket left, bracket right]
          _                    ->
            case termView left of
              ConstView c ->
                let name = constantDescriptionQualifiedName c in
                let unic = get unicode thy in
                  case M.lookup name unic of
                    Nothing -> unwords [bracket left, bracket right]
                    Just en ->
                      case en of
                        NoFix sym binder ->
                          if binder then
                            case termView right of
                              LamView name ty body ->
                                if showTypes then
                                  let ty' = unicodeTypeInTheory thy ty in
                                    sym ++ "(" ++ name ++ " : " ++ ty' ++ "). " ++ bracket body
                                else
                                  sym ++ name ++ ". " ++ bracket body
                              _                    -> unwords [sym, bracket right]
                          else
                            unwords [sym, bracket right]
                        Postfix sym         -> unwords [bracket right, sym]
                        _                   -> unwords [bracket left, bracket right]
              _              -> unwords [bracket left, bracket right]
      go (termView->LamView n ty body) =
        if showTypes then
          let ty' = unicodeTypeInTheory thy ty in
            "λ" ++ "(" ++ n ++ " : " ++ ty' ++ "). " ++ bracket body
          else
            "λ" ++ n ++ ". " ++ bracket body
      go (termView->ConstView c) =
        let name = constantDescriptionQualifiedName c in
        let unic = get unicode thy in
          case M.lookup name unic of
            Nothing -> qualifiedNameHead name
            Just en ->
              case en of
                NoFix sym binder -> sym
                Infix sym        -> sym
                Postfix sym      -> sym
      go (termView->VarView v ty) = v

  unicodeTypeInTheory :: Theory -> Type -> String
  unicodeTypeInTheory thy = go
    where
      bracket :: Type -> String
      bracket typ =
        if size typ > 1 then
          "(" ++ go typ ++ ")"
        else
          go typ

      go :: Type -> String
      go (typeView->TyVarView var)          = var
      go (typeView->TyOperatorView op args) =
        let name = typeOperatorDescriptionQualifiedName op in
        let unic = get unicode thy in
          case M.lookup name unic of
            Nothing ->
              if length args == 0 then
                qualifiedNameHead name
              else
                qualifiedNameHead name ++ (unwords . map bracket $ args)
            Just en ->
              case en of
                Infix sym ->
                  case args of
                    [l, r] -> unwords [bracket l, sym, bracket r]
                    _      -> sym ++ (unwords . map bracket $ args)
                Postfix sym ->
                  (unwords . map bracket $ args) ++ sym
                NoFix sym binder -> sym ++ (unwords . map bracket $ args)

  unicodeTheoremInTheory :: Theory -> ShowTypes -> Theorem -> String
  unicodeTheoremInTheory thy showTypes thm =
    let hyps = L.intercalate ", " . map (unicodeTermInTheory thy showTypes) . hypotheses $ thm in
    let conc = unicodeTermInTheory thy showTypes $ conclusion thm in
      unwords [hyps, "⊢", conc]

  latexTermInTheory :: Theory -> ShowTypes -> Term -> String
  latexTermInTheory thy showTypes = go
    where

      bracket :: Term -> String
      bracket trm =
        if size trm > 1 then
          "(" ++ go trm ++ ")"
        else
          go trm

      go :: Term -> String
      go (termView->AppView left right) =
        case termView left of
          AppView left' right' ->
            case termView left' of
              ConstView c ->
                let name = constantDescriptionQualifiedName c in
                let unic = get latex thy in
                  case M.lookup name unic of
                    Nothing -> L.intercalate "\\ " [bracket left, bracket right]
                    Just en ->
                      case en of
                        NoFix sym binder ->
                          if binder then
                            case termView right' of
                              LamView name ty body ->
                                if showTypes then
                                  let ty' = latexTypeInTheory thy ty in
                                    sym ++ "(" ++ name ++ " : " ++ ty' ++ ").\\ " ++ bracket body ++ bracket right
                                else
                                  sym ++ "{" ++ name ++ "}.\\ " ++ bracket body ++ bracket right
                              _                    -> L.intercalate "\\ " [sym, bracket right', bracket right]
                          else
                            L.intercalate "\\ " [sym, bracket right', bracket right]
                        Postfix sym         -> L.intercalate "\\ " [bracket left, bracket right, sym]
                        Infix sym           -> L.intercalate "\\ " [bracket right', sym, bracket right]
              _              -> L.intercalate "\\ " [bracket left, bracket right]
          _                    ->
            case termView left of
              ConstView c ->
                let name = constantDescriptionQualifiedName c in
                let unic = get latex thy in
                  case M.lookup name unic of
                    Nothing -> L.intercalate "\\ " [bracket left, bracket right]
                    Just en ->
                      case en of
                        NoFix sym binder ->
                          if binder then
                            case termView right of
                              LamView name ty body ->
                                if showTypes then
                                  let ty' = latexTypeInTheory thy ty in
                                    sym ++ "(" ++ name ++ " : " ++ ty' ++ ").\\ " ++ bracket body
                                else
                                  sym ++ "{" ++ name ++ "}.\\ " ++ bracket body
                              _                    -> L.intercalate "\\ " [sym, bracket right]
                          else
                            L.intercalate "\\ " [sym, bracket right]
                        Postfix sym         -> L.intercalate "\\ " [bracket right, sym]
                        _                   -> L.intercalate "\\ " [bracket left, bracket right]
              _              -> L.intercalate "\\ " [bracket left, bracket right]
      go (termView->LamView n ty body) =
        if showTypes then
          let ty' = latexTypeInTheory thy ty in
            "\\lambda" ++ "(" ++ n ++ " : " ++ ty' ++ ").\\ " ++ bracket body
          else
            "\\lambda{" ++ n ++ "}.\\ " ++ bracket body
      go (termView->ConstView c) =
        let name = constantDescriptionQualifiedName c in
        let unic = get latex thy in
          case M.lookup name unic of
            Nothing -> qualifiedNameHead name
            Just en ->
              case en of
                NoFix sym binder -> sym
                Infix sym        -> sym
                Postfix sym      -> sym
      go (termView->VarView v ty) = v

  latexTypeInTheory :: Theory -> Type -> String
  latexTypeInTheory thy = go
    where
      bracket :: Type -> String
      bracket typ =
        if size typ > 1 then
          "(" ++ go typ ++ ")"
        else
          go typ

      go :: Type -> String
      go (typeView->TyVarView var)          = var
      go (typeView->TyOperatorView op args) =
        let name = typeOperatorDescriptionQualifiedName op in
        let unic = get latex thy in
          case M.lookup name unic of
            Nothing ->
              if length args == 0 then
                qualifiedNameHead name
              else
                qualifiedNameHead name ++ (unwords . map bracket $ args)
            Just en ->
              case en of
                Infix sym ->
                  case args of
                    [l, r] -> unwords [bracket l, sym, bracket r]
                    _      -> sym ++ (unwords . map bracket $ args)
                Postfix sym ->
                  (unwords . map bracket $ args) ++ sym
                NoFix sym binder -> sym ++ (unwords . map bracket $ args)

  latexTheoremInTheory :: Theory -> ShowTypes -> Theorem -> String
  latexTheoremInTheory thy showTypes thm =
    let hyps = L.intercalate ",\\ " . map (latexTermInTheory thy showTypes) . hypotheses $ thm in
    let conc = latexTermInTheory thy showTypes $ conclusion thm in
      unwords [hyps, "\\vdash", conc]
