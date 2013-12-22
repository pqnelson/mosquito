{-# LANGUAGE TemplateHaskell, TypeOperators, DoAndIfThenElse #-}

-- |The Mosquito proof state for tracking the current state during
--  a backwards (tactic-oriented) proof.  Functions for making an
--  initial conjecture, applying pretactics to a proof state, and
--  for retrieving a theorem from a complete backwards proof.
module Mosquito.ProofState.ProofState (
  -- * Proof state configurations
  ProofStateConfiguration,
  prettyPrint, showTypes, selectNewGoals,
  defaultProofStateConfiguration,
  -- * Preliminary notions
  Tag,
  Justification, PreTactic, TermPreTactic, TheoremPreTactic,
  Tactic, TheoremTactic, TermTactic,
  ProofStep(..),
  -- * Proof states
  ProofTree, ProofState,
  -- * Utility functions on proof states
  countOpen, countSelected,
  getAllGoals, getSelectedGoals,
  -- * Basic stackticals
  selectITac, selectPTac,
  -- * Conjecturing and refining in backwards proof
  conjecture, conjectureWithConfiguration,
  apply, qed
)
where

  import Prelude hiding (fail)

  import qualified Control.Monad.State as State

  import Data.Label
  import qualified Data.List as L
  import qualified Data.Set as S

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  --
  -- * Settings for proof status configuration
  --

  data ProofStateConfiguration
    = ProofStateConfiguration {
      _prettyPrint    :: Bool
    , _showTypes      :: Bool
    , _selectNewGoals :: Bool
    } deriving (Eq)

  mkLabels [''ProofStateConfiguration]

  -- |The default proof state configuration, used in "conjecture".
  defaultProofStateConfiguration :: ProofStateConfiguration
  defaultProofStateConfiguration =
    ProofStateConfiguration {
      _prettyPrint    = True
    , _showTypes      = True
    , _selectNewGoals = True
    }

  -- |Returns a pretty printing or show function depending on the
  --  configuration settings in "ProofStateConfiguration".
  prettyConfig :: (Show a, Pretty a) => ProofStateConfiguration -> a -> String
  prettyConfig config
    | get prettyPrint config = pretty
    | otherwise              = show

  --
  -- * Preliminary notions, and type synonyms for export.
  --

  -- |Tags whether a subgoal is selected or unselected.  Selection
  --  status of a goal can be changed with the primitive stackticals
  --  provided below, or with the more advanced stackticals built
  --  on top of those in @Stackticals.hs@.
  data Tag
    = Selected
    | Unselected
      deriving (Eq, Show, Ord)

  -- |The "view" for the incomplete derivation tree being refined
  --  during a backwards proof.  User written pretactics/tactics
  --  perform their editing action on this data structure rather
  --  than the real derivation tree which remains abstract outside
  --  of this module.
  data ProofStep
    = Refine Justification [ProofStep]
    | Open [Theorem] Term

  -- |A justification function is used to convert a complete proof
  --  tree into a theorem, by working forwards from the leaves of
  --  the tree towards a final theorem.  Every tactic needs to
  --  supply a justification function, it's inverse operation, to
  --  retrieve a theorem from the resulting incomplete proof state
  --  the tactic generates.
  type Justification = [Theorem] -> Inference Theorem

  -- |A pretactic receives a list of theorems (the assumptions of
  --  a goal) and the goal itself (a Boolean-typed term), and either
  --  fails of produces a refinement of the incomplete derivation
  --  tree using the @ProofStep@ data type.
  type PreTactic = [Theorem] -> Term -> Inference ProofStep

  -- |A @TheoremPreTactic@ is a function that takes a @Theorem@ and
  --  returns a @PreTactic@.
  type TheoremPreTactic = Theorem -> PreTactic

  -- |A @TermPreTactic@ is a function that takes a @Term@ and returns
  --  a @PreTactic@.
  type TermPreTactic = Term -> PreTactic

  -- |A @Tactic@ takes a @ProofState@ and produces another @ProofState@
  --  or fails.
  type Tactic = ProofState -> Inference ProofState

  -- |A @TheoremTactic@ is a function that takes a @Theorem@ and
  --  returns a @Tactic@.
  type TheoremTactic = Theorem -> Tactic

  -- |A @TermTactic@ is a function that takes a @Term@ and
  --  returns a @Tactic@.
  type TermTactic = Term -> Tactic

  --
  -- * The proof state proper
  --

  -- |The @ProofTree@ is an abstract type outside of this module
  --  that encapsulates the incomplete derivation tree being built
  --  by a backwards proof.  A @Hole@ corresponds to a goal yet to
  --  be proved.  A @Leaf@ corresponds to a goal that has been
  --  solved by a @Theorem@.  A @Node@ corresponds to a family of
  --  of open goals that can be "undone" with a @Justification@
  --  function.  Note that @Leaf@ is really a special case of
  --  @Node@.
  data ProofTree
    = Hole Tag [Theorem] Term
    | Leaf Theorem
    | Node Justification [ProofTree]

  instance Show ProofTree where
    show (Hole tag assms concl) =
      unwords [
        "Hole", show tag, show assms, show concl
      ]
    show (Leaf theorem) =
      unwords [
        "Leaf", show theorem
      ]
    show (Node _ children) =
      unwords [
        "Node", "Justification", show children
      ]

  -- |Equality on a @ProofTree@ proceeds pointwise, ignoring
  --  @Justification@ functions which are incomparable.
  instance Eq ProofTree where
    (Hole tag assms concl) == (Hole tag' assms' concl') =
      tag == tag' && assms == assms' && concl == concl'
    (Leaf thm) == (Leaf thm') = thm == thm'
    (Node _ children) == (Node _ children') = children == children'
    _ == _ = False

  -- |A @ProofState@ consists of the name of the current conjecture
  --  (just used for pretty printing the proof state), the initial
  --  goal (a Boolean-typed term) which is used to check the "qed"
  --  of the final proof state is correct, and a derivation tree
  --  corresponding to the incomplete proof state.
  data ProofState
    = ProofState {
      _name          :: String
    , _goal          :: Term
    , _derivation    :: ProofTree
    , _configuration :: ProofStateConfiguration
    } deriving (Eq)

  mkLabels [''ProofState]

  --
  -- ** Utility functions on proof states.
  --

  -- |Returns the number of open goals in a @ProofState@.
  countOpen :: ProofState -> Int
  countOpen = go . get derivation
    where
      go :: ProofTree -> Int
      go Hole{}            = 1
      go Leaf{}            = 0
      go (Node _ children) =
        sum . map go $ children

  -- |Returns the number of selected open goals in a @ProofState@.
  countSelected :: ProofState -> Int
  countSelected = go . get derivation
    where
      go (Hole Selected _ _) = 1
      go Hole{}              = 0
      go Leaf{}              = 0
      go (Node _ children)   =
        sum . map go $ children

  -- |Returns the set of all open goals (as represented by a list
  --  of assumptions coupled with a Boolean-typed term) in a
  --  @ProofState@.
  getAllGoals :: ProofState -> S.Set ([Theorem], Term)
  getAllGoals state = go $ get derivation state
    where
      go :: ProofTree -> S.Set ([Theorem], Term)
      go (Hole _ assms concl) = S.singleton (assms, concl)
      go Leaf{} = S.empty
      go (Node _ children) =
        S.unions . map go $ children

  -- |Returns a list of selected goals (represented by a list
  --  of assumptions coupled with a Boolean-typed term) in a
  --  @ProofState@.  The ordering of this returned list should
  --  always remain in lockstep with the numbering of selected
  --  goals (so the first element of the list is Goal 0 in the
  --  proofstate).
  getSelectedGoals :: ProofState -> [([Theorem], Term)]
  getSelectedGoals state = go $ get derivation state
    where
      go :: ProofTree -> [([Theorem], Term)]
      go (Hole tag assms concl)
        | tag == Selected  = return (assms, concl)
        | otherwise        = []
      go Leaf{} = []
      go (Node _ children) =
        concatMap go children

  -- |For internal use in pretty printing the current goal
  --  state only.  Returns a list of pretty printed goals
  --  and their goal number.
  --  XXX: rewrite this to make use of the function above?
  getPrettySelectedGoals :: ProofState -> [(Int, String)]
  getPrettySelectedGoals state = State.evalState (go $ get derivation state) 0
    where
      config :: ProofStateConfiguration
      config = get configuration state

      go :: ProofTree -> State.State Int [(Int, String)]
      go t@Hole{} = do
        index <- State.get
        State.modify (+ 1)
        return . return $ (index, prettyConfig config t)
      go Leaf{} = return []
      go (Node _ children) = do
        mChildren <- State.mapM go children
        return . concat $ mChildren

  prettySelected :: [(Int, String)] -> String
  prettySelected =
    L.intercalate "\n" . map (\(index, p) -> unwords ["[", show index, "]", p])

  --
  -- * Building and modifying a proof state.
  --

  -- |Makes a conjecture.  A conjecture consists of a String name
  --  (with no real significance, whose only use is in pretty-printing
  --  the goal state) and a @Term@.  The term must be Boolean-typed
  --  otherwise the function fails.  Otherwise, all being well, an
  --  initial @ProofState@ is created.  This is the only way of
  --  creating an initial proof state.  A configuration argument is
  --  passed to control how pretty printing, and other options, are
  --  used.
  conjectureWithConfiguration :: ProofStateConfiguration -> String -> Term -> Inference ProofState
  conjectureWithConfiguration config nm goal = do
    typeOfGoal <- typeOf goal
    if typeOfGoal == boolType then
      return $ ProofState {
        _name          = nm
      , _goal          = goal
      , _derivation    = Hole tag [] goal
      , _configuration = config
      }
    else
      fail . unwords $ [
        "Cannot conjecture a term of non-boolean type.  Was expecting"
      , unwords ["term: `", prettyConfig config goal, "'to have type bool"]
      , unwords ["in conjecture `", nm, "'."]
      ]
    where
      tag :: Tag
      tag =
        if get selectNewGoals config then
          Selected
        else
          Unselected

  -- |Makes a conjecture with the default configuration.
  conjecture :: String -> Term -> Inference ProofState
  conjecture = conjectureWithConfiguration defaultProofStateConfiguration

  -- |Lifts a @PreTactic@ to a @Tactic@ by applying the pretactic to
  --  all selected open goals in a proof state.
  apply :: PreTactic -> Tactic
  apply pre status = do
      tree <- go pre $ get derivation status
      if tree == get derivation status then
        fail "No change in `apply'."
      else
        return $ set derivation tree status
    where

      refineProofTree :: ProofStep -> Inference ProofTree
      refineProofTree (Refine j []) = do
        thm <- j []
        return $ Leaf thm
      refineProofTree (Refine j children) = do
        trees <- mapM refineProofTree children
        return $ Node j trees
      refineProofTree (Open assms concl) =
        return $ Hole tag assms concl

      tag :: Tag
      tag =
        if get selectNewGoals . get configuration $ status then
          Selected
        else
          Unselected

      go :: PreTactic -> ProofTree -> Inference ProofTree
      go ptac prooftree =
        case prooftree of
          t@(Hole Selected assms concl) -> do
            edit <- ptac assms concl
            refineProofTree edit
--            inference (ptac assms concl)
--              (const . return $ t)
--              refineProofTree
          Hole{}                        -> return prooftree
          Leaf{}                        -> return prooftree
          (Node j children)             -> do
            mChildren <- mapM (go ptac) children
            return $ Node j mChildren

  -- |Retrieves a @Theorem@ from a @ProofState@.  For this to be
  --  successful, the proof state needs to have no open goals
  --  (i.e. no @Hole@ appears in the derivation tree) and the
  --  result of applying and combining all of the forward-acting
  --  justification functions must match the initial conjecture
  --  stored in the proof state.  All being well, the @Theorem@
  --  resulting from the justification function application is
  --  returned.
  qed :: ProofState -> Inference Theorem
  qed status =
    if open == 0 then do
      thm <- go $ get derivation status
      if conclusion thm == get goal status then
        return thm
      else
        fail . unwords $ [
          "The proof cannot be completed because the initial"
        , unwords ["goal `", prettyConfig config (get goal status), "' does not"]
        , "match the conclusion of the generated theorem derived"
        , unwords ["from the proof: `", prettyConfig config (conclusion thm), "'."]
        ]
    else
      fail $ unwords [
        "Cannot `qed' an incomplete derivation, when attempting to"
      , unwords ["complete proof of `", prettyConfig config (get goal status), "'."]
      , unwords ["In particular", show open, "open goals persist. They are:\n"]
      ] ++ (prettySelected . getPrettySelectedGoals $ status)
    where
      open :: Int
      open = countOpen status

      config :: ProofStateConfiguration
      config = get configuration status

      go :: ProofTree -> Inference Theorem
      go Hole{}     =
        fail . unwords $ [
          "BUG: in `qed'.  Please report."
        ]
      go (Leaf thm) = return thm
      go (Node j children) = do
        mChildren <- mapM go children
        thm       <- j mChildren
        return thm

  --
  -- * Selecting goals (basic stackticals)
  --

  -- |Selects goals based on a predicate on the list of
  --  assumptions and term corresponding to a goal.  All goals
  --  failing the test are marked unselected.
  selectPTac :: ([Theorem] -> Term -> Bool) -> Tactic
  selectPTac p = return . modify derivation walk
    where
      walk :: ProofTree -> ProofTree
      walk (Hole _ assms concl)
        | p assms concl      = Hole Selected   assms concl
        | otherwise          = Hole Unselected assms concl
      walk (Node j children) =
        Node j $ map walk children
      walk (Leaf thm)        = Leaf thm

  -- |Selects goals based on a predicate on the number of
  --  a goal.  All goals failing the test are marked as unselected.
  selectITac :: (Int -> Bool) -> Tactic
  selectITac p = return . modify derivation ((flip State.evalState) 0 . walk)
    where
      walk :: ProofTree -> State.State Int ProofTree
      walk (Hole _ assms concl) = do
        index <- State.get
        State.modify (+ 1)
        if p index then
          return $ Hole Selected   assms concl
        else
          return $ Hole Unselected assms concl
      walk (Leaf theorem) = return . Leaf $ theorem
      walk (Node j children) = do
        mChildren <- mapM walk children
        return $ Node j mChildren

  --
  -- * Pretty printing proof states.
  --

  instance Pretty ProofTree where
    pretty (Leaf l) =
      unwords ["Goal closed by theorem `", pretty l, "'."]
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
    pretty (Node _ trees) =
      L.intercalate "\n\n" . map pretty $ trees

  instance Pretty ProofState where
    pretty status =
        L.intercalate "\n" [
          unwords ["Attempting to prove conjecture `", get name status, "'."]
        , unwords ["Goals:", show $ countOpen status, "open with", show $ countSelected status, "selected."]
        , prettySelected . getPrettySelectedGoals $ status
        ]