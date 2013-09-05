{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Mosquito.ProofState (
  Tag, ProofTree, ProofStatus,
  Justification, PreTactic, TermPreTactic, TheoremPreTactic,
  Tactic, TheoremTactic, TermTactic,
  ProofStep(..),
  open, selected,
  conjecture, apply, qed
)
where

  import Prelude hiding (fail)

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

  type Tactic = ProofStatus -> Inference ProofStatus
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

  data ProofStatus
    = ProofStatus {
      _name       :: String,
      _goal       :: Term,
      _derivation :: ProofTree
    } deriving (Eq)

  mkLabels [''ProofStatus]

  open :: ProofStatus -> Int
  open = go . get derivation
    where
      go :: ProofTree -> Int
      go Hole{}            = 1
      go Leaf{}            = 0
      go (Node _ children) =
        sum . map go $ children

  selected :: ProofStatus -> Int
  selected = go . get derivation
    where
      go (Hole Selected _ _) = 1
      go Hole{}              = 0
      go Leaf{}              = 0
      go (Node _ children)   =
        sum . map go $ children

  conjecture :: String -> Term -> Inference ProofStatus
  conjecture name goal = do
    typeOfGoal <- typeOf goal
    if typeOfGoal == boolType then
      return $ ProofStatus {
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
        return $ Hole Selected assms concl

      go :: PreTactic -> ProofTree -> Inference ProofTree
      go pre prooftree =
        case prooftree of
          (Hole Selected assms concl) ->
            case pre assms concl of
              Fail err -> Fail err
              Success r -> refineProofTree r
          h@Hole{}                    -> return prooftree
          l@Leaf{}                    -> return prooftree
          n@(Node j children)         -> do
            children <- mapM (go pre) children
            return $ Node j children

  qed :: ProofStatus -> Inference Theorem
  qed status =
    if open status == 0 then do
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

  instance Pretty ProofTree where
    pretty (Leaf l) =
      unwords ["Goal closed by theorem `", pretty l, "'."]
    pretty (Hole tag assms concl) =
      if null assms then
        L.intercalate "\n" [
          unwords ["Show", selected]
        , unwords ["\t⊢ˀ", pretty concl]
        ]
      else
        L.intercalate "\n" [
          "Assuming:"
        , (L.intercalate "\n" . map pretty $ assms)
        , unwords ["Show", selected]
        , unwords ["\t⊢ˀ", pretty concl]
        ]
      where
        selected :: String
        selected =
          case tag of
            Selected -> "(selected subgoal):"
            _        -> "(subgoal not selected):"
    pretty (Node j trees) =
      L.intercalate "\n\n" . map pretty $ trees

  instance Pretty ProofStatus where
    pretty status =
      L.intercalate "\n" [
        unwords ["Attempting to prove conjecture `", get name status, "'."]
      , unwords ["Goals:", show $ open status, "open with", show $ selected status, "selected."]
      , pretty $ get derivation status
      ]     