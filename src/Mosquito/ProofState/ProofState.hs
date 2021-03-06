{-# LANGUAGE TemplateHaskell, GADTs, DoAndIfThenElse #-}

-- |The Mosquito proof state for tracking the current state during
--  a backwards (tactic-oriented) proof.  Functions for making an
--  initial conjecture, applying pretactics to a proof state, and
--  for retrieving a theorem from a complete backwards proof.
module Mosquito.ProofState.ProofState (
  Selection(..),
  IncompleteDerivation,
  ProofState,
  mkConjecture, mkConjectureRule, qed,
  act,
  unicodeProofStateInTheory
) where

  import Prelude hiding (fail, repeat)

  import qualified Control.Monad.State as State

  import Data.Label
  import qualified Data.List as L hiding (repeat)

  import Mosquito.Kernel.Term

  import Mosquito.ProofState.PreTactics
  import Mosquito.ProofState.Tactics hiding (repeat, try, apply)

  import Mosquito.Theories.Theory

  import Mosquito.Utility.Pretty

  data Selection where
    Selected   :: Selection
    Unselected :: Selection

  data IncompleteDerivation where
    Hole   :: Selection     -> [Term] -> Term -> IncompleteDerivation
    Branch :: Justification -> [IncompleteDerivation] -> IncompleteDerivation

  data ProofState
    = ProofState {
      _conjectureName :: String
    , _conjecture     :: Term
    , _derivation     :: IncompleteDerivation
    }

  mkLabels [''ProofState]

  -- * Conjecturing and completing proofs

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
      fail . unwords $ [
        "mkConjecture: cannot conjecture a non-propositional term: `", pretty conjecture, "'."
      ]

  mkConjectureRule:: String -> [Term] -> Term -> Inference ProofState
  mkConjectureRule name hyps conjecture = do
    conjectureType <- typeOf conjecture
    if isProposition conjectureType then
      return $ ProofState {
        _conjectureName = name
      , _conjecture     = conjecture
      , _derivation     = Hole Selected hyps conjecture
      }
    else
      fail . unwords $ [
        "mkConjecture: cannot conjecture a non-propositional term: `", pretty conjecture, "'."
      ]

  qed :: ProofState -> Inference Theorem
  qed = go . get derivation
    where
      go :: IncompleteDerivation -> Inference Theorem
      go Hole{}                    = fail "Cannot `qed' an incomplete derivation."
      go (Branch justification []) = justification []
      go (Branch justification xs) = do
        xs' <- mapM go xs
        justification xs'

  -- * Progressing the proof

  apply :: PreTactic -> IncompleteDerivation -> Inference IncompleteDerivation
  apply tactic (Hole Selected assms goal) = do
    let editor = get localEdit tactic
    (justification, children) <- editor assms goal
    let children' = map (uncurry $ Hole Selected) children
    return $ Branch justification children'
  apply tactic t@(Hole Unselected assms goal) = return t
  apply tactic (Branch justification children) = do
    children' <- mapM (apply tactic) children
    return $ Branch justification children'

  applyTrace :: PreTactic -> IncompleteDerivation -> Inference (IncompleteDerivation, [String])
  applyTrace tactic derivation = do
    derivation <- apply tactic derivation
    return (derivation, return . unwords $ ["Applying `", pretty tactic, "' at `", pretty derivation, "'."])

  try :: Tactic -> IncompleteDerivation -> IncompleteDerivation
  try tactical h@(Hole Selected assms concl) =
    inference (dispatch tactical h)
      (const h)
      id
  try tactical h@(Hole Unselected assms concl) = h
  try tactical (Branch justification children) =
    Branch justification $ map (try tactical) children

  followedBy :: Tactic -> Tactic -> IncompleteDerivation -> Inference IncompleteDerivation
  followedBy left right derivation = do
    left' <- dispatch left derivation
    dispatch right left'

  choice :: Tactic -> Tactic -> IncompleteDerivation -> Inference IncompleteDerivation
  choice left right derivation =
    inference (dispatch left derivation)
      (const $ dispatch right derivation)
      return

  repeat :: Tactic -> IncompleteDerivation -> Inference IncompleteDerivation
  repeat tactical derivation =
    inference (dispatch tactical derivation)
      (const . return $ derivation)
      (\d -> go tactical d derivation)
    where
      go :: Tactic -> IncompleteDerivation -> IncompleteDerivation -> Inference IncompleteDerivation
      go tactical derivation fixed =
        inference (dispatch tactical derivation)
          (const . return $ fixed)
          (\d -> go tactical d derivation)

  dispatch :: Tactic -> IncompleteDerivation -> Inference IncompleteDerivation
  dispatch (Apply tactic)          derivation = apply tactic derivation
  dispatch (FollowedBy left right) derivation = followedBy left right derivation
  dispatch (Try tactical)          derivation = return $ try tactical derivation
  dispatch Id                      derivation = return derivation
  dispatch (FailWith err)          derivation = fail err
  dispatch (Choice left right)     derivation = choice left right derivation
  dispatch (Repeat tactical)       derivation = repeat tactical derivation

  act :: ProofState -> Tactic -> Inference ProofState
  act proofState tactical = do
    derivation' <- dispatch (optimise tactical) $ get derivation proofState
    return $ set derivation derivation' proofState

  debug :: ProofState -> Tactic -> (Inference ProofState, Maybe Tactic)
  debug proofState Id             = (return proofState, Nothing)
  debug proofState (FailWith err) = (fail err, Nothing)
  debug proofState (FollowedBy left right) =
    inference (act proofState left)
      (\err   -> (fail err, Nothing))
      (\state -> (return state, Just right))
  debug proofState (Choice left right) =
    inference (act proofState left)
      (const (return proofState, Just right))
      (\state -> (return state, Nothing))
  debug proofState (Try tactical) =
    inference (act proofState tactical)
      (const (return proofState, Nothing))
      (\state -> (return state, Nothing))
  debug proofState (Repeat tactical) =
    inference (act proofState tactical)
      (const (return proofState, Nothing))
      (\state -> go state proofState tactical)
    where
      go :: ProofState -> ProofState -> Tactic -> (Inference ProofState, Maybe Tactic)
      go new fixed tactic =
        inference (act new tactic)
          (const (return fixed, Nothing))
          (\state -> (return state, Just tactic))


  -- * Printing the proof state

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
        , unwords ["\t??????", pretty concl]
        ]
      else
        L.intercalate "\n" [
          "Assuming:"
        , (L.intercalate "\n" . map pretty $ assms)
        , selected
        , unwords ["\t??????", pretty concl]
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

  unicodeIncompleteDerivationInTheory :: Theory -> ShowTypes -> IncompleteDerivation -> String
  unicodeIncompleteDerivationInTheory thy showTypes (Hole tag assms concl) =
    if null assms then
      L.intercalate "\n" [
        selected
      , unwords ["\t??????", unicodeTermInTheory thy showTypes concl]
      ]
    else
      L.intercalate "\n" [
        "Assuming:"
      , (L.intercalate "\n" . map (unicodeTermInTheory thy showTypes) $ assms)
      , selected
      , unwords ["\t??????", unicodeTermInTheory thy showTypes concl]
      ]
    where
      selected :: String
      selected =
        case tag of
          Selected -> "selected subgoal."
          _        -> "subgoal not selected."
  unicodeIncompleteDerivationInTheory thy showTypes (Branch _ children) =
    L.intercalate "\n\n" . map (unicodeIncompleteDerivationInTheory thy showTypes) $ children

  getUnicodeSelectedGoalsInTheory :: Theory -> ShowTypes -> ProofState -> [(Int, String)]
  getUnicodeSelectedGoalsInTheory thy showTypes state = State.evalState (go $ get derivation state) 0
    where
      go :: IncompleteDerivation -> State.State Int [(Int, String)]
      go t@Hole{} = do
        index <- State.get
        State.modify (+ 1)
        return . return $ (index, unicodeIncompleteDerivationInTheory thy showTypes t)
      go (Branch _ children) = do
        mChildren <- State.mapM go children
        return . concat $ mChildren

  unicodeProofStateInTheory :: Inference Theory -> ShowTypes -> Inference ProofState -> Inference String
  unicodeProofStateInTheory thy showTypes state = do
    thy   <- thy
    state <- state
    return $ L.intercalate "\n" [
      unwords ["Attempting to prove conjecture `", get conjectureName state, "'."]
      , unwords ["Goals:", show $ countOpen state, "open with", show $ countSelected state, "selected."]
      , prettySelected . getUnicodeSelectedGoalsInTheory thy showTypes $ state
      ]