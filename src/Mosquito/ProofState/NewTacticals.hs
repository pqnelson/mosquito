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

  import Debug.Trace

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

  instance Show Tactic where
    show = get tacticName

  data Tactical where
    Apply      :: Tactic   -> Tactical
    Try        :: Tactical -> Tactical
    FollowedBy :: Tactical -> Tactical -> Tactical
    Id         :: Tactical
    Choice     :: Tactical -> Tactical -> Tactical
    Repeat     :: Tactical -> Tactical
      deriving Show

  (<*>) :: Tactical -> Tactical -> Tactical
  left <*> right = left `FollowedBy` right

  (<|>) :: Tactical -> Tactical -> Tactical
  left <|> right = left `Choice` right

  repeatN :: Int -> Tactic -> Tactical
  repeatN 0 tactic = Id
  repeatN m tactic = Apply tactic <*> repeatN (m - 1) tactic

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

  optimise :: Tactical -> Tactical
  optimise (FollowedBy left Id)                = optimise left
  optimise (FollowedBy Id right)               = optimise right
  optimise (Repeat Id)                         = Id
  optimise (FollowedBy (Try left) (Try right)) =
    Try (FollowedBy (optimise left) (optimise right))
  optimise tactical = tactical

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

      repeat :: Tactical -> IncompleteDerivation -> Inference IncompleteDerivation
      repeat tactical derivation =
        inference (dispatch tactical derivation)
          (const . return $ derivation)
          (\d -> go tactical d derivation)
        where
          go :: Tactical -> IncompleteDerivation -> IncompleteDerivation -> Inference IncompleteDerivation
          go tactical derivation fixed =
            inference (dispatch tactical derivation)
              (const . return $ fixed)
              (\d -> go tactical d derivation)

      dispatch :: Tactical -> IncompleteDerivation -> Inference IncompleteDerivation
      dispatch (Apply tactic)          derivation = apply tactic derivation
      dispatch (Try   tactical)        derivation = return $ try tactical derivation
      dispatch (FollowedBy left right) derivation = followedBy left right derivation
      dispatch Id                      derivation = return derivation
      dispatch (Choice left right)     derivation = choice left right derivation
      dispatch (Repeat tactical)       derivation = repeat tactical derivation

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

  abstractPreTactic :: PreTactic
  abstractPreTactic assms concl = do
    (l, r)             <- fromEquality concl
    (name,  ty, lBody) <- fromLam l
    (name', _,  rBody) <- fromLam r
    if name == name' then do
      nConcl <- mkEquality lBody rBody
      return (\[t] -> abstract name ty t, [(assms, nConcl)])
    else do
      let nBody =  permute name name' rBody
      nConcl    <- mkEquality lBody nBody
      return (\[t] -> abstract name ty t, [(assms, nConcl)])

  abstractTactic :: Tactic
  abstractTactic =
      Tactic {
        _tacticName = "abstractTactic"
      , _preTactic  = abstractPreTactic
      }

  combinePreTactic :: PreTactic
  combinePreTactic assms concl = do
    (left, right)    <- fromEquality concl
    (leftL, leftR)   <- fromApp left
    (rightL, rightR) <- fromApp right
    nLeft            <- mkEquality leftL rightL
    nRight           <- mkEquality leftR rightR
    return (\[t, t'] -> combine t t', [(assms, nLeft), (assms, nRight)])

  combineTactic :: Tactic
  combineTactic =
    Tactic {
      _tacticName = "combineTactic"
    , _preTactic  = combinePreTactic
    }

  solvePreTactic :: TheoremPreTactic
  solvePreTactic thm _ concl =
    if conclusion thm == concl then
      return (\[] -> return thm, [])
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

  equalityModusPonensPreTactic :: TermPreTactic
  equalityModusPonensPreTactic guess assms concl = do
    eq <- mkEquality guess concl
    return $ (\[t, t'] -> equalityModusPonens t t', [(assms, eq), (assms, guess)])

  equalityModusPonensTactic :: Term -> Tactic
  equalityModusPonensTactic guess =
    Tactic {
      _tacticName = "equalityModusPonensTactic"
    , _preTactic  = equalityModusPonensPreTactic guess
    }

  pointwiseTactical :: Tactical
  pointwiseTactical = Repeat (Apply abstractTactic <|> Apply combineTactic) <*> autoBaseTactical

  unfoldTactical :: Theorem -> Tactical
  unfoldTactical thm = Apply localTac <*> (Try pointwiseTactical) <*> (Try $ autoSolveTactical thm)
    where
      replace :: ConstantDescription -> Term -> Term -> Inference Term
      replace dom rng t =
        if isApp t then do
          (l, r) <- fromApp t
          nL     <- replace dom rng l
          nR     <- replace dom rng r
          mkApp nL nR
        else if isLam t then do
          (n, ty, body) <- fromLam t
          nBody <- replace dom rng body
          return $ mkLam n ty nBody
        else if isConst t then do
          descr <- fromConst t
          if descr == dom then
            return rng
          else
            return t
        else return t

      local :: PreTactic
      local assms concl = do
        (left, right) <- fromEquality . conclusion $ thm
        if isConst left then do
          c     <- fromConst left
          guess <- replace c right concl
          equalityModusPonensPreTactic guess assms concl
        else if isConst right then do
          c     <- fromConst right
          guess <- replace c left concl
          equalityModusPonensPreTactic guess assms concl
        else
          fail "`unfoldTac'"

      localTac :: Tactic
      localTac =
        Tactic {
          _tacticName = "unfoldTactic"
        , _preTactic  = local
        }