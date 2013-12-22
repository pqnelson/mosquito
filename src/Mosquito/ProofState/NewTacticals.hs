{-# LANGUAGE GADTs, TemplateHaskell #-}

module Mosquito.ProofState.NewTacticals
where

  import Prelude hiding (fail)

  import Control.Arrow
  import Control.Monad hiding (fail)
  import qualified Control.Monad.State as State

  import Data.Label
  import qualified Data.List as L
  import qualified Data.Set as S

  import Mosquito.DerivedRules
  import Mosquito.Kernel.Term
  import Mosquito.Kernel.QualifiedName
  import Mosquito.Utility.Pretty

  data Selection where
    Selected   :: Selection
    Unselected :: Selection

  type Justification    = [Theorem] -> Inference Theorem
  type PreTactic        = [Theorem] -> Term -> Inference (Justification, [([Theorem], Term)])
  type TermPreTactic    = Term -> PreTactic
  type TheoremPreTactic = Theorem -> PreTactic

  data Tactic
    = Tactic {
      _tacticName :: String
    , _preTactic  :: PreTactic
    }

  mkLabels [''Tactic]

  data Tactical where
    Apply      :: Tactic   -> Tactical
    Try        :: Tactical -> Tactical
    FollowedBy :: Tactical -> Tactical -> Tactical
    Id         :: Tactical
    Choice     :: Tactical -> Tactical -> Tactical

  (<*>) :: Tactical -> Tactical -> Tactical
  left <*> right = left `FollowedBy` right

  (<|>) :: Tactical -> Tactical -> Tactical
  left <|> right = left `Choice` right

  by :: [Tactical] -> Tactical
  by = foldr (<*>) Id

  data IncompleteDerivation where
    Hole   :: Selection     -> [Theorem] -> Term -> IncompleteDerivation
    Branch :: Justification -> [IncompleteDerivation] -> IncompleteDerivation

  data ProofState
    = ProofState {
      _conjectureName :: String
    , _conjecture     :: Term
    , _derivation     :: IncompleteDerivation
    }

  mkLabels [''ProofState]

  mkConjecture :: String -> Term -> Inference ProofState
  mkConjecture name conjecture = do
    conjectureType <- typeOf conjecture
    if isProposition conjectureType then
      return $ ProofState {
        _conjectureName = name
      , _conjecture     = conjecture
      , _derivation     = Hole Selected [] conjecture
      }
    else
      fail $ "Cannot conjecture a non-propositional term."

  act :: Tactical -> ProofState -> Inference ProofState
  act tactical proofState = do
      derivation' <- dispatch tactical $ get derivation proofState
      return $ set derivation derivation' proofState
    where
      apply :: Tactic -> IncompleteDerivation -> Inference IncompleteDerivation
      apply tactic (Hole Selected assms goal) = do
        let pretactic = get preTactic tactic
        (justification, children) <- pretactic assms goal
        let children' = map (\(x, y) -> Hole Selected x y) children
        return $ Branch justification children'
      apply tactic t@(Hole Unselected assms goal) = return t
      apply tactic (Branch justification children) = do
        children' <- mapM (apply tactic) children
        return $ Branch justification children'

      try :: Tactical -> IncompleteDerivation -> IncompleteDerivation
      try tactical h@(Hole Selected assms concl) =
        inference (dispatch tactical h)
          (const h)
          id
      try tactical h@(Hole Unselected assms concl) = h
      try tactical (Branch justification children) =
        Branch justification $ map (try tactical) children

      followedBy :: Tactical -> Tactical -> IncompleteDerivation -> Inference IncompleteDerivation
      followedBy left right derivation = do
        left' <- dispatch left derivation
        dispatch right left'

      choice :: Tactical -> Tactical -> IncompleteDerivation -> Inference IncompleteDerivation
      choice left right derivation =
        inference (dispatch left derivation)
          (const $ dispatch right derivation)
          return

      dispatch :: Tactical -> IncompleteDerivation -> Inference IncompleteDerivation
      dispatch (Apply tactic)          derivation = apply tactic derivation
      dispatch (Try   tactical)        derivation = return $ try tactical derivation
      dispatch (FollowedBy left right) derivation = followedBy left right derivation
      dispatch Id                      derivation = return derivation
      dispatch (Choice left right)     derivation = choice left right derivation

  qed :: ProofState -> Inference Theorem
  qed = go . get derivation
    where
      go :: IncompleteDerivation -> Inference Theorem
      go Hole{}                    = fail "Cannot `qed' an incomplete derivation."
      go (Branch justification []) = justification []
      go (Branch justification xs) = do
        xs' <- mapM go xs
        justification xs'

  countOpen :: ProofState -> Int
  countOpen = go . get derivation
    where
      go :: IncompleteDerivation -> Int
      go Hole{}            = 1
      go (Branch _ children) =
        sum . map go $ children

  -- |Returns the number of selected open goals in a @ProofState@.
  countSelected :: ProofState -> Int
  countSelected = go . get derivation
    where
      go :: IncompleteDerivation -> Int
      go (Hole Selected _ _) = 1
      go Hole{}              = 0
      go (Branch _ children)   =
        sum . map go $ children

  getPrettySelectedGoals :: ProofState -> [(Int, String)]
  getPrettySelectedGoals state = State.evalState (go $ get derivation state) 0
    where
      go :: IncompleteDerivation -> State.State Int [(Int, String)]
      go t@Hole{} = do
        index <- State.get
        State.modify (+ 1)
        return . return $ (index, pretty t)
      go (Branch _ children) = do
        mChildren <- State.mapM go children
        return . concat $ mChildren

  prettySelected :: [(Int, String)] -> String
  prettySelected =
    L.intercalate "\n" . map (\(index, p) -> unwords ["[", show index, "]", p])

  instance Pretty IncompleteDerivation where
    pretty (Hole tag assms concl) =
      if null assms then
        L.intercalate "\n" [
          selected
        , unwords ["\t⊢﹖", pretty concl]
        ]
      else
        L.intercalate "\n" [
          "Assuming:"
        , (L.intercalate "\n" . map pretty $ assms)
        , selected
        , unwords ["\t⊢﹖", pretty concl]
        ]
      where
        selected :: String
        selected =
          case tag of
            Selected -> "selected subgoal."
            _        -> "subgoal not selected."
    pretty (Branch _ children) =
      L.intercalate "\n\n" . map pretty $ children

  instance Pretty ProofState where
    pretty proofState =
        L.intercalate "\n" [
          unwords ["Attempting to prove conjecture `", get conjectureName proofState, "'."]
        , unwords ["Goals:", show $ countOpen proofState, "open with", show $ countSelected proofState, "selected."]
        , prettySelected . getPrettySelectedGoals $ proofState
        ]

  --
  -- Testing
  --

  constantOfDecl :: Inference (Term, a) -> Inference Term
  constantOfDecl = liftM fst

  theoremOfDecl :: Inference (a, Theorem) -> Inference Theorem
  theoremOfDecl = liftM snd

  trueDecl :: Inference (Term, Theorem)
  trueDecl = do
    let name =  mkQualifiedName ["Mosquito", "Bool"] "true"
    let t    =  mkLam "a" boolType $ mkVar "a" boolType
    eq       <- mkEquality t t
    primitiveNewDefinedConstant name eq boolType

  trueC :: Inference Term
  trueC = constantOfDecl trueDecl

  trueD :: Inference Theorem
  trueD = theoremOfDecl trueDecl

  betaReduce :: Term -> Inference Term
  betaReduce t = do
    (left, right) <- fromApp t
    (n, _, body)  <- fromLam left
    return $ termSubst n right body

  alphaPreTactic :: PreTactic
  alphaPreTactic assms concl = do
    (left, right) <- fromEquality concl
    if left == right then do
      return $ (\[] -> alpha left right, [])
    else
      fail $ "`alphaPreTactic'"

  symmetryPreTactic :: PreTactic
  symmetryPreTactic assms concl = do
    (l, r) <- fromEquality concl
    nConcl <- mkEquality r l
    return $ (\[t] -> symmetry t, [(assms, nConcl)])

  etaPreTactic :: PreTactic
  etaPreTactic _ concl = do
    (left, _) <- fromEquality concl
    --- XXX: test here
    thm <- eta left
    return $ (\[] -> return thm, [])

  betaPreTactic :: PreTactic
  betaPreTactic _ concl = do
    (left, right) <- fromEquality concl
    reduced       <- betaReduce left
    if reduced == right then do
      thm <- beta left
      return $ (\[] -> return thm, [])
    else
      fail "`betaPreTac'"

  alphaTactic :: Tactic
  alphaTactic =
    Tactic {
      _tacticName = "alphaTactic"
    , _preTactic  = alphaPreTactic
    }

  symmetryTactic :: Tactic
  symmetryTactic =
    Tactic {
      _tacticName = "symmetryTactic"
    , _preTactic  = symmetryPreTactic
    }

  etaTactic :: Tactic
  etaTactic =
    Tactic {
      _tacticName = "etaTactic"
    , _preTactic  = etaPreTactic
    }

  betaTactic :: Tactic
  betaTactic =
    Tactic {
      _tacticName = "betaTactic"
    , _preTactic  = betaPreTactic
    }

  solvePreTactic :: TheoremPreTactic
  solvePreTactic thm _ concl =
    if conclusion thm == concl then
      return $ (\[] -> return thm, [])
    else
      fail "`solvePreTac'"

  solveTactic :: Theorem -> Tactic
  solveTactic thm =
    Tactic {
      _tacticName = "solveTactic"
    , _preTactic  = solvePreTactic thm
    }

  autoSolveTactical :: Theorem -> Tactical
  autoSolveTactical thm =
    Apply (solveTactic thm) <|> (Apply symmetryTactic <*> Apply (solveTactic thm))

  autoBaseTactical :: Tactical
  autoBaseTactical = autoEtaTactical <|> (autoBetaTactical <|> Apply alphaTactic)
    where
      autoBetaTactical :: Tactical
      autoBetaTactical = Apply betaTactic <|> (Apply symmetryTactic <*> Apply betaTactic)

      autoEtaTactical :: Tactical
      autoEtaTactical = Apply etaTactic <|> (Apply symmetryTactic <*> Apply etaTactic)

  test = Mosquito.Utility.Pretty.putStrLn $ do
    trueC <- trueC
    trueD <- trueD
    goal  <- mkEquality trueC trueC
    conj  <- mkConjecture "test" trueC
    conj  <- act (Try autoBaseTactical) conj
    conj  <- act (autoSolveTactical trueD) conj
    return conj