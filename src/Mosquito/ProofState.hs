{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Mosquito.ProofState (
  Tag, ProofTree, ProofState,
  Justification, PreTactic, TermPreTactic, TheoremPreTactic,
  Tactic, TheoremTactic, TermTactic,
  ProofStep(..),
  countOpen, countSelected,
  selectITac, selectPTac,
  conjecture, apply, qed
)
where

  import Prelude hiding (fail)

  import qualified Control.Monad.State as S

  import Mosquito.Kernel.Term

  import Mosquito.Utility.Pretty

  import Data.Label
  import qualified Data.List as L

  data ProofStep
    = Refine Justification [ProofStep]
    | Open [Theorem] Term

  type Justification = [Theorem] -> Inference Theorem
  type PreTactic = [Theorem] -> Term -> Inference ProofStep
  type TheoremPreTactic = Theorem -> PreTactic
  type TermPreTactic = Term -> PreTactic

  type Tactic = ProofState -> Inference ProofState
  type TheoremTactic = Theorem -> Tactic
  type TermTactic = Term -> Tactic

  data Tag
    = Selected
    | Unselected
      deriving (Eq, Show, Ord)

  data ProofTree
    = Hole Tag [Theorem] Term
    | Leaf Theorem
    | Node Justification [ProofTree]

  instance Eq ProofTree where
    (Hole tag assms concl) == (Hole tag' assms' concl') =
      tag == tag' && assms == assms' && concl == concl'
    (Leaf thm) == (Leaf thm') = thm == thm'
    (Node _ children) == (Node _ children') = children == children'

  data ProofState
    = ProofState {
      _name       :: String,
      _goal       :: Term,
      _derivation :: ProofTree
    } deriving (Eq)

  mkLabels [''ProofState]

  countOpen :: ProofState -> Int
  countOpen = go . get derivation
    where
      go :: ProofTree -> Int
      go Hole{}            = 1
      go Leaf{}            = 0
      go (Node _ children) =
        sum . map go $ children

  countSelected :: ProofState -> Int
  countSelected = go . get derivation
    where
      go (Hole Selected _ _) = 1
      go Hole{}              = 0
      go Leaf{}              = 0
      go (Node _ children)   =
        sum . map go $ children

  getSelectedGoals :: ProofState -> [(Int, String)]
  getSelectedGoals state = S.evalState (go $ get derivation state) 0
    where
      go :: ProofTree -> S.State Int [(Int, String)]
      go t@(Hole tag assms concl) = do
        index <- S.get
        S.modify (+ 1)
        return . return $ (index, pretty t)
      go Leaf{} = do
        index <- S.get
        return []
      go (Node j children) = do
        children <- S.mapM go children
        return . concat $ children

  --
  -- * Building and modifying a proof state
  --

  conjecture :: String -> Term -> Inference ProofState
  conjecture name goal = do
    typeOfGoal <- typeOf goal
    if typeOfGoal == boolType then
      return $ ProofState {
        _name       = name,
        _goal       = goal,
        _derivation = Hole Selected [] goal
      }
    else
      fail . unwords $ [
        "Cannot conjecture a term of non-boolean type.  Was expecting"
      , unwords ["term: `", pretty goal, "'to have type bool"]
      , unwords ["in conjecture `", name, "'."]
      ]

  apply :: PreTactic -> Tactic
  apply pre status = do
      tree <- go pre (get derivation status)
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
        return $ Hole Unselected assms concl

      go :: PreTactic -> ProofTree -> Inference ProofTree
      go pre prooftree =
        case prooftree of
          t@(Hole Selected assms concl) ->
            case pre assms concl of
              Fail err -> return t
              Success r -> refineProofTree r
          h@Hole{}                    -> return prooftree
          l@Leaf{}                    -> return prooftree
          n@(Node j children)         -> do
            children <- mapM (go pre) children
            return $ Node j children

  qed :: ProofState -> Inference Theorem
  qed status =
    if countOpen status == 0 then do
      thm <- go $ get derivation status
      if conclusion thm == get goal status then
        return thm
      else
        fail . unwords $ [
          "The proof cannot be completed because the initial"
        , unwords ["goal `", pretty (get goal status), "' does not"]
        , "match the conclusion of the generated theorem derived"
        , unwords ["from the proof: `", pretty (conclusion thm), "'."]
        ]
    else
      fail . unwords $ [
        "Cannot `qed' an incomplete derivation, when attempting to"
      , unwords ["complete proof of `", pretty (get goal status), "'."]
      ]
    where
      go :: ProofTree -> Inference Theorem
      go Hole{}     =
        fail . unwords $ [
          "BUG: in `qed'.  Please report."
        ]
      go (Leaf thm) = return thm
      go (Node j children) = do
        children <- mapM go children
        thm      <- j children
        return thm

  --
  -- * Selecting goals
  --

  selectPTac :: ([Theorem] -> Term -> Bool) -> Tactic
  selectPTac pred state = return $ modify derivation (walk pred) state
    where
      walk :: ([Theorem] -> Term -> Bool) -> ProofTree -> ProofTree
      walk pred (Hole tag assms concl)
        | pred assms concl = Hole Selected assms concl
        | otherwise        = Hole tag assms concl
      walk pred (Node j children) =
        Node j $ map (walk pred) children

  selectITac :: (Int -> Bool) -> Tactic
  selectITac pred state = return $ modify derivation (\d -> S.evalState (walk pred d) 0) state
    where
      walk :: (Int -> Bool) -> ProofTree -> S.State Int ProofTree
      walk pred (Hole tag assms concl) = do
        index <- S.get
        S.modify (+ 1)
        if pred index then
          return $ Hole Selected assms concl
        else
          return $ Hole tag assms concl
      walk pred (Leaf theorem) = return $ Leaf theorem
      walk pred (Node j children) = do
        children <- mapM (walk pred) children
        return $ Node j children

  instance Pretty ProofTree where
    pretty (Leaf l) =
      unwords ["Goal closed by theorem `", pretty l, "'."]
    pretty (Hole tag assms concl) =
      if null assms then
        L.intercalate "\n" [
          selected
        , unwords ["\t⊢ˀ", pretty concl]
        ]
      else
        L.intercalate "\n" [
          "Assuming:"
        , (L.intercalate "\n" . map pretty $ assms)
        , selected
        , unwords ["\t⊢ˀ", pretty concl]
        ]
      where
        selected :: String
        selected =
          case tag of
            Selected -> "selected subgoal."
            _        -> "subgoal not selected."
    pretty (Node j trees) =
      L.intercalate "\n\n" . map pretty $ trees

  instance Pretty ProofState where
    pretty status =
        L.intercalate "\n" [
          unwords ["Attempting to prove conjecture `", get name status, "'."]
        , unwords ["Goals:", show $ countOpen status, "open with", show $ countSelected status, "selected."]
        , prettySelected . getSelectedGoals $ status
        ]
      where
        prettySelected :: [(Int, String)] -> String
        prettySelected =
          L.intercalate "\n" . map (\(index, pretty) -> unwords ["[", show index, "]", pretty])