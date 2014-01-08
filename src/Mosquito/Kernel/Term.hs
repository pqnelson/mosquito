{-# LANGUAGE DoAndIfThenElse #-}

-- |The Mosquito kernel, defining types, terms, theorems, and providing primitive
--  inference rules upon which everything else is built, along with simple mechanisms
--  for extending the Mosquito logic (e.g. declaring axioms, defining new types and
--  constants).
--
--  Everything in this file is considered trusted, that is, to trust the logical
--  soundness and consistency of the whole system you must trust that this file correctly
--  implements a version of classical, extensional higher-order logic, a la HOL4 and
--  Isabelle/HOL.  Due to the internal representation of terms, types and theorems not
--  being exposed to the rest of the system (via Haskell's abstraction mechanisms),
--  and with terms, types and theorems being correct by contruction (if this file is
--  bug free), consistency of the whole system is guaranteed (the so-called LCF
--  approach).
module Mosquito.Kernel.Term (
  -- * Some useful definitions
  Arity, Definition,
  -- * The inference monad
  Inference, fail, inference, userMark,
  -- * Type operator descriptions
  TypeOperatorDescription,
  isDefinedTypeOperatorDescription, isPrimitiveTypeOperatorDescription,
  typeOperatorDescriptionArity, typeOperatorDescriptionQualifiedName,
  typeOperatorDescriptionDefinition,
  boolQualifiedName, functionQualifiedName,
  boolDescription, functionDescription,
  -- * HOL types
  Type,
  isTyVar, isTyOperator, isFunction, isProposition,
  fromTyOperator, fromTyVar, fromFunction,
  mkTyVar, mkTyOperator,
  alphaName, alphaType, boolType,
  mkFunctionType,
  -- * Constant descriptions
  ConstantDescription,
  isDefinedConstantDescription, isPrimitiveConstantDescription,
  constantDescriptionType, constantDescriptionQualifiedName, constantDescriptionDefinition,
  equalityType, equalityQualifiedName, equalityDescription,
  -- * HOL terms
  Term,
  mkVar, mkConst, mkApp, mkLam,
  isVar, isConst, isApp, isLam,
  fromVar, fromConst, fromApp, fromLam,
  -- ** Type checking
  typeOf,
  -- ** Alpha-equivalence and free variables
  fv, fvs, permute,
  -- ** Structural equality
  StructuralEquality, mkStructuralEquality,
  -- ** Equality within the logic
  equality, isEquality,
  fromEquality, mkEquality,
  -- ** Type substitutions
  typeSubst,
  -- ** Term substitutions
  termSubst, termTypeSubst,
  -- * HOL theorems
  Provenance,
  track,
  Theorem,
  hypotheses, conclusion, provenance,
  union, delete, deleteTheorem,
  -- ** Basic HOL theorems
  alpha, symmetry, transitivity, abstract, combine, eta, beta,
  assume, equalityModusPonens, deductAntiSymmetric,
  typeInstantiation, instantiation,
  -- * Extending the logic
  primitiveNewDefinedConstant, primitiveNewAxiom
)
where

  -- import Prelude (Bool(..), String)
  import Prelude hiding (fail)

  import qualified Data.Foldable as F
  import qualified Data.List as L
  import qualified Data.Set as S

  import Mosquito.Kernel.QualifiedName

  import Mosquito.Utility.Pretty

  --
  -- * Some useful type synonyms and functions
  --

  -- |Type representing the arity of type operators and constants.
  type Arity = Int

  -- |Type representing definitions of defined types and constants.
  type Definition = Term

  --
  -- * The inference monad
  --

  data ITag
    = FromKernel
    | OutwithKernel
      deriving Eq

  -- |The inference monad, an error monad used throughout Mosquito to signal
  --  success or failure of a computation.
  data Inference a
    = Fail    [(ITag, String)] String
    | Success [(ITag, String)] a

  -- |An elimination principle for the Inference monad.
  inference :: Inference a -> (String -> b) -> (a -> b) -> b
  inference (Fail _ err)    f _ = f err
  inference (Success _ t) _ s = s t

  -- |A function signifying a failing computation within the Inference monad.
  --  Parameter is the error message that will be displayed when the error
  --  is encountered at top-level.
  fail :: String -> Inference a
  fail = Fail []

  instance Pretty a => Pretty (Inference a) where
    pretty (Fail trace err) =
      L.intercalate "\n" $ [
        "*** ERROR:"
      , err
      , "*** CALL TRACE:"
      ] ++ map (\(tag, t) ->
        case tag of
          FromKernel -> "  [Kernel call]:" ++ "\t" ++ t
          OutwithKernel -> "[Userspace call]:" ++ "\t" ++ t
        ) (reverse trace)
    pretty (Success count t) =
      L.intercalate "\n" [
        unwords["Computation successful in `", show . length . filter (\x -> fst x == FromKernel) $ count, "' primitive inference steps:"]
      , pretty t
      ]

  instance Monad Inference where
    return                  = Success []
    (Fail trace err)        >>= _ = Fail trace err
    (Success trace t) >>= f =
      case f t of
        Fail trace' err -> Fail (trace ++ trace') err
        Success trace' t -> Success (trace ++ trace') t

  kernelMark :: [String] -> Inference ()
  kernelMark s = Success [(FromKernel, L.intercalate "\t\t\t" s)] ()

  userMark :: [String] -> Inference ()
  userMark s = Success [(OutwithKernel, L.intercalate "\t\t\t" s)] ()

  --
  -- * Type operator descriptions.
  --

  -- |The 'TypeOperatorDescription' type describes HOL type operators.  Type
  --  operators are either primitive (in the case of the type of propositions
  --  and the function space arrow) or are defined.  Defined type operators
  --  carry a definition around with them.
  data TypeOperatorDescription
    = DefinedTypeOperator   QualifiedName Arity Definition
    | PrimitiveTypeOperator QualifiedName Arity
    deriving(Eq, Show, Ord)

  --
  -- ** Utility functions on type operator descriptions.
  --

  -- |Tests whether the description refers to a defined, rather than a primitive,
  --  type operator description.
  isDefinedTypeOperatorDescription :: TypeOperatorDescription -> Bool
  isDefinedTypeOperatorDescription DefinedTypeOperator{} = True
  isDefinedTypeOperatorDescription _                     = False

  -- |Tests whether the description refers to a primitive, rather than defined,
  --  type operator description.
  isPrimitiveTypeOperatorDescription :: TypeOperatorDescription -> Bool
  isPrimitiveTypeOperatorDescription PrimitiveTypeOperator{} = True
  isPrimitiveTypeOperatorDescription _                       = False

  -- |Retrieves the arity of a type operator description.
  typeOperatorDescriptionArity :: TypeOperatorDescription -> Arity
  typeOperatorDescriptionArity (DefinedTypeOperator _ a _) = a
  typeOperatorDescriptionArity (PrimitiveTypeOperator _ a) = a

  -- |Retrieves the name of a type operator description.
  typeOperatorDescriptionQualifiedName :: TypeOperatorDescription -> QualifiedName
  typeOperatorDescriptionQualifiedName (DefinedTypeOperator n _ _) = n
  typeOperatorDescriptionQualifiedName (PrimitiveTypeOperator n _) = n

  -- |Retrieves the definition of a defined type operator description.  If the
  --  description is a primitive type operator, then the function returns 
  --  'Nothing'.
  typeOperatorDescriptionDefinition :: TypeOperatorDescription -> Maybe Definition
  typeOperatorDescriptionDefinition (DefinedTypeOperator _ _ d) = return d
  typeOperatorDescriptionDefinition PrimitiveTypeOperator{}     = Nothing

  --
  -- ** Type operator descriptions corresponding to the primitive HOL type
  --    operators, and building new descriptions.
  --

  -- |The name of the primitive HOL bool type.
  boolQualifiedName :: QualifiedName
  boolQualifiedName = mkQualifiedName ["Mosquito"] "Bool"

  -- |The name of the primitive HOL function space type operator.
  functionQualifiedName :: QualifiedName
  functionQualifiedName = mkQualifiedName ["Mosquito"] "_→_"

  -- |The description of the primitive HOL bool type.
  boolDescription :: TypeOperatorDescription
  boolDescription = PrimitiveTypeOperator boolQualifiedName 0

  -- |The description of the primitive HOL function space type former.
  functionDescription :: TypeOperatorDescription
  functionDescription = PrimitiveTypeOperator functionQualifiedName 2

  --
  -- ** Pretty printing type operator descriptions
  --

  instance Pretty TypeOperatorDescription where
    pretty = pretty . typeOperatorDescriptionQualifiedName

  --
  -- * HOL types
  --

  -- |The type of HOL types.  Types are either type variables, or are operators
  --  which when applied to a list of other types, the length of which must
  --  match the arity proscribed, form another type.
  data Type
    = TyVar      String
    | TyOperator TypeOperatorDescription [Type]
    deriving(Eq, Show, Ord)

  --
  -- ** Utility functions on types.
  --

  -- |Tests whether a Type is a type variable.
  isTyVar :: Type -> Bool
  isTyVar TyVar{} = True
  isTyVar _       = False

  -- |Tests whether a Type is a type operator.
  isTyOperator :: Type -> Bool
  isTyOperator TyOperator{} = True
  isTyOperator _            = False

  -- |Tests whether a Type is a function type.
  isFunction :: Type -> Bool
  isFunction (TyOperator f [_, _]) = f == functionDescription
  isFunction _                     = False

  -- |Tests whether a Type is a propositional (Boolean) type.
  isProposition :: Type -> Bool
  isProposition (TyOperator b []) = b == boolDescription
  isProposition _                 = False

  -- |Deconstructs a type operator into its TypeOperatorDescription and
  --  [Type] components, failing with an error message if the input Type is
  --  not a type operator otherwise.
  fromTyOperator :: Type -> Inference (TypeOperatorDescription, [Type])
  fromTyOperator (TyOperator d args) = return (d, args)
  fromTyOperator t = fail $ "fromTyOperator: Type `" ++ pretty t ++ "' is not a type operator."

  -- |Makes a type operator from a TypeOperatorDescription and a list of
  --  Type.  Fails with an error message if the input list length differs
  --  from the declared arity of the TypeOperatorDescription.
  mkTyOperator :: TypeOperatorDescription -> [Type] -> Inference Type
  mkTyOperator d ts = do
    if length ts == typeOperatorDescriptionArity d
      then
        return $ TyOperator d ts
      else
        fail . unwords $ [
          "mkTyOperator: Length of type arguments passed to `mkTyOperator' does not ",
          "match the declared arity of the type description passed, ",
          "declared arity: " ++ show (typeOperatorDescriptionArity d),
          " versus: " ++ show (length ts) ++ " supplied."
        ]

  -- |Collects the free type variables of a type (by definition, as we have
  --  no binding of type variables in types in Mosquito, all occurrences of
  --  type variables in a type are deemed free) into a Set.
  tv :: Type -> S.Set String
  tv (TyVar v)           = S.singleton v
  tv (TyOperator _ args) = L.foldr S.union S.empty $ map tv args 

  --
  -- ** Some basic types.
  --

  -- |Utility: the name of the alpha type variable, used quite often (but
  --  entirely arbitrarily) throghout Mosquito.
  alphaName :: String
  alphaName = "α"

  -- |The type variable corresponding to the alphaName above.
  alphaType :: Type
  alphaType = TyVar alphaName

  -- |The Boolean type.
  boolType :: Type
  boolType = TyOperator boolDescription []

  -- |Makes a type variable from a String.
  mkTyVar :: String -> Type
  mkTyVar = TyVar
  
  -- |Deconstructs a type variable into its String component, failing
  --  with an error message if the input Type is not a type variable
  --  otherwise.
  fromTyVar :: Type -> Inference String
  fromTyVar (TyVar v) = return v
  fromTyVar t         = fail $ "fromTyVar: Type `" ++ pretty t ++ "' is not a type variable."

  -- |Utility function for constructing a function type from two previously
  --  defined types.
  mkFunctionType :: Type -> Type -> Type
  mkFunctionType d r = TyOperator functionDescription [d, r]

  -- |Deconstructs a function type into its domain and range types, failing
  --  with an error message if the input Type is not a function type otherwise.
  fromFunction :: Type -> Inference (Type, Type)
  fromFunction t@(TyOperator (PrimitiveTypeOperator f 2) [d, r])
    | f == functionQualifiedName = return (d, r)
    | otherwise                  = fail . unwords $ ["fromFunction: Type `", pretty t, "' is not a function type."]
  fromFunction t = fail . unwords $ ["fromFunction: Type `", pretty t, "' is not a function type."]

  --
  -- ** Pretty printing types.
  --

  instance Size Type where
    size TyVar{}             = 1
    size (TyOperator _ args) = 1 + length args

  instance Pretty Type where
    pretty (TyVar v)                 = v
    pretty (TyOperator descr [d, r])
      | descr == functionDescription = bracket d ++ " → " ++ bracket r
      | otherwise                    = unwords [pretty descr, bracket d, bracket r]
    pretty (TyOperator descr args)   =
      if null args then
        pretty descr
      else
        pretty descr ++ " " ++ (unwords . map bracket $ args)

  --
  -- * Constant descriptions.
  --

  -- |The description of constants defined within the Mosquito logic.  Mosquito
  --  constants fall into one of two types: primitive, such as equality, or
  --  defined, which are defined by the user (following suitable checks to ensure
  --  consistency remains).  All constants have a qualified name and type.
  --  Defined constants also keep hold of the defining term used in their
  --  definition to ensure that inconsistencies caused by mixing and matching
  --  constants of the same name but defined in different proof assistant states
  --  cannot creep into the system.
  data ConstantDescription
    = DefinedConstant   QualifiedName Type Definition
    | PrimitiveConstant QualifiedName Type
    deriving(Eq, Show, Ord)

  --
  -- * Utility functions on constant descriptions.
  --

  -- |Tests whether a ConstantDescription is defined.
  isDefinedConstantDescription :: ConstantDescription -> Bool
  isDefinedConstantDescription DefinedConstant{} = True
  isDefinedConstantDescription _                 = False

  -- |Tests whether a ConstantDescription is primitive.
  isPrimitiveConstantDescription :: ConstantDescription -> Bool
  isPrimitiveConstantDescription PrimitiveConstant{} = True
  isPrimitiveConstantDescription _                   = False

  -- |Returns the qualified name of a ConstantDescription.
  constantDescriptionQualifiedName :: ConstantDescription -> QualifiedName
  constantDescriptionQualifiedName (DefinedConstant n _ _) = n
  constantDescriptionQualifiedName (PrimitiveConstant n _) = n

  -- |Returns the type of a ConstantDescription.
  constantDescriptionType :: ConstantDescription -> Type
  constantDescriptionType (DefinedConstant _ t _) = t
  constantDescriptionType (PrimitiveConstant _ t) = t

  -- |Returns the definition of a defined ConstantDescription.  Fails
  --  if the ConstantDescription is primitive.
  constantDescriptionDefinition :: ConstantDescription -> Maybe Definition
  constantDescriptionDefinition (DefinedConstant _ _ d) = return d
  constantDescriptionDefinition PrimitiveConstant{}     = Nothing

  --
  -- * Some useful predefined constant descriptions.
  --

  -- |Qualified name of the (primitive) equality constant baked into
  --  Mosquito's higher-order logic.
  equalityQualifiedName :: QualifiedName
  equalityQualifiedName = mkQualifiedName ["Mosquito"] "_=_"

  -- |Polymorphic type of the equality constant.
  equalityType :: Type
  equalityType = mkFunctionType alphaType $ mkFunctionType alphaType boolType

  -- |ConstantDescription describing Mosquito's equality constant.
  equalityDescription :: ConstantDescription
  equalityDescription = PrimitiveConstant equalityQualifiedName equalityType

  --
  -- ** Pretty printing constant descriptions
  --

  instance Pretty ConstantDescription where
    pretty d
      | isInfix . constantDescriptionQualifiedName $ d = partialInfixKernel . constantDescriptionQualifiedName $ d
      | otherwise = qualifiedNameHead . constantDescriptionQualifiedName $ d

  --
  -- * HOL terms.
  --

  -- |The type of HOL terms, explicitly-typed Church-style terms of
  -- the lambda-calculus extended with constants.
  data Term
    = Var   String Type
    | Const ConstantDescription
    | App   Term Term
    | Lam   String Type Term
    deriving(Show, Ord)

  --
  -- * Utility functions on terms.
  --

  -- |Tests whether a Term is a variable.
  isVar :: Term -> Bool
  isVar Var{} = True
  isVar _     = False

  -- |Tests whether a Term is a constant.
  isConst :: Term -> Bool
  isConst Const{} = True
  isConst _       = False

  -- |Tests whether a Term is an application.
  isApp :: Term -> Bool
  isApp App{} = True
  isApp _     = False

  -- |Tests whether a Term is a lambda-abstraction.
  isLam :: Term -> Bool
  isLam Lam{} = True
  isLam _     = False

  -- |Makes a variable.
  mkVar :: String -> Type -> Term
  mkVar = Var

  -- |Makes a constant.
  mkConst :: ConstantDescription -> Term
  mkConst = Const

  -- |Makes an application.  Fails if there is a type mismatch between
  --  the two arguments.
  mkApp :: Term -> Term -> Inference Term
  mkApp l r = do
    typeOfL  <- typeOf l
    typeOfR  <- typeOf r
    (dom, _) <- fromFunction typeOfL
    if dom == typeOfR
      then
        return $ App l r
      else
        fail . unwords $ [
          "mkApp: Right hand term passed to `mkApp' does not have type matching",
          "domain type of left hand term.  Expecting `" ++ pretty dom ++ "'",
          "but found `" ++ pretty typeOfR ++ "'."
        ]

  -- |Makes a lambda-abstraction.
  mkLam :: String -> Type -> Term -> Term
  mkLam = Lam

  -- |Deconstructs a term, succeeding if the term is a variable, failing otherwise.
  fromVar :: Term -> Inference (String, Type)
  fromVar (Var v ty) = return (v, ty)
  fromVar t          = fail . unwords $ ["fromVar: Input term `", pretty t, "' is not a variable."]

  -- |Deconstructs a term, succeeding if the term is a constant, failing otherwise.
  fromConst :: Term -> Inference ConstantDescription
  fromConst (Const c) = return c
  fromConst t         = fail . unwords $ ["fromConst: Input term `", pretty t, "' is not a constant."]

  -- |Deconstructs a term, succeeding if the term is an application, failing otherwise.
  fromApp :: Term -> Inference (Term, Term)
  fromApp (App l r) = return (l, r)
  fromApp t         = fail . unwords $ ["fromApp: Input term `", pretty t, "' is not an application."]

  -- |Deconstructs a term, succeeding if the term is a lambda-abstraction, failing otherwise.
  fromLam :: Term -> Inference (String, Type, Term)
  fromLam (Lam a ty bdy) = return (a, ty, bdy)
  fromLam t              = fail . unwords $ ["fromLam: Input term `", pretty t, "' is not an abstraction."]

  --
  -- ** Equality
  --

  -- |The equality constant.
  equality :: Term
  equality = Const equalityDescription

  -- |Tests whether a term is an equality.
  isEquality :: Term -> Bool
  isEquality (App (App (Const d) _) _) = constantDescriptionQualifiedName d == equalityQualifiedName
  isEquality _                         = False

  -- |Makes an equality.  Fails if there is a type mismatch between the two
  --  arguments and the equality constant.
  mkEquality :: Term -> Term -> Inference Term
  mkEquality l r = do
    typeOfL <- typeOf l
    typeOfR <- typeOf r
    if typeOfL == typeOfR then do
      left <- mkApp (termTypeSubst "α" typeOfL equality) l
      mkApp left r
    else
      fail . unwords $ [
        "mkEquality: Types of the left and right hand sides of the proposed equality do"
      , "not match, in a call to `mkEquality'.  Specifically, left hand side"
      , unwords ["has type `", pretty typeOfL, "' whilst right hand side has type"]
      , unwords ["`", pretty typeOfR, "'."]
      ]

  -- |Deconstructs a term, succeeding if the term was an equality, failing otherwise.
  fromEquality :: Term -> Inference (Term, Term)
  fromEquality t@(App (App (Const d) c) r)
    | constantDescriptionQualifiedName d == equalityQualifiedName = return (c, r)
    | otherwise                                                   =
        fail . unwords $ ["fromEquality: Input term `", pretty t, "' is not an equality."]
  fromEquality t    = fail . unwords $ ["fromEquality: Input term `", pretty t, "' is not an equality."]

  --
  -- * Type checking.
  --

  typeOf :: Term -> Inference Type
  typeOf (Var _ ty) = return ty
  typeOf (Const d)  = return . constantDescriptionType $ d
  typeOf (App l r)  = do
    lTy        <- typeOf l
    rTy        <- typeOf r
    (dom, rng) <- fromFunction lTy
    if dom == rTy
      then
        return rng
      else
        fail . unwords $ [
          unwords ["typeOf: Domain type of `", pretty l, "' and type of `", pretty r, "'"]
        , unwords ["do not match.  Was expecting `", pretty lTy, "' but found"]
        , unwords ["`", pretty rTy, "'."]
        ]
  typeOf (Lam _ ty bdy) = do
    bodyTy <- typeOf bdy
    return $ mkFunctionType ty bodyTy

  --
  -- * Substitutions and utility functions
  --

  -- |Perform a type substitution replacing type variables whose names match
  --  the first argument with the second argument.
  typeSubst :: String -> Type -> Type -> Type
  typeSubst dom rng (TyVar v)
    | dom == v  = rng
    | otherwise = TyVar v
  typeSubst dom rng (TyOperator descr args) =
    TyOperator descr . map (typeSubst dom rng) $ args

  -- |Performs a type substitution on all types decorating the term (at lambda
  --  binding sites, within constant declarations and on decorating types
  --  appearing on variables).
  termTypeSubst :: String -> Type -> Term -> Term
  termTypeSubst dom rng (Var v ty) = Var v $ typeSubst dom rng ty
  termTypeSubst dom rng (Const c)  = Const . go $ c
    where
      go :: ConstantDescription -> ConstantDescription
      go (PrimitiveConstant n ty) = PrimitiveConstant n $ typeSubst dom rng ty
      go (DefinedConstant n ty d) = DefinedConstant n (typeSubst dom rng ty) d
  termTypeSubst dom rng (App l r)  =
    App (termTypeSubst dom rng l) $ termTypeSubst dom rng r
  termTypeSubst dom rng (Lam a ty body) =
    Lam a (typeSubst dom rng ty) $ termTypeSubst dom rng body

  fresh :: S.Set String -> String
  fresh = go "f" 0
    where
      go :: String -> Integer -> S.Set String -> String
      go suggested counter seen
        | suggested `S.member` seen = go (suggested ++ show counter) (counter + 1) seen
        | otherwise                 = suggested

  -- |Performs a capture-avoiding term substitution with fresh-name generation
  --  if necessary.
  termSubst :: String -> Term -> Term -> Term
  termSubst dom rng (Var v ty)
    | dom == v  = rng
    | otherwise = Var v ty
  termSubst _ _ (Const c) = Const c
  termSubst dom rng (App l r) = App (termSubst dom rng l) (termSubst dom rng r)
  termSubst dom rng t@(Lam a ty body)
    | a == dom || a `S.member` fv rng =
      let freshName = fresh $ S.unions [S.singleton dom, variables rng, variables t] in
        Lam freshName ty $ termSubst dom rng $ permute a freshName body
    | otherwise = Lam a ty $ termSubst dom rng body

  --
  -- ** Alpha-equivalence on terms.
  --

  -- |Collects all variables, including bound variables, appearing within
  --  a term into a set.  Used for fresh name generation, where we do not
  --  want any clashes of freshened bound variables with bound variables
  --  existing under the binder.
  variables :: Term -> S.Set String
  variables (Var a _)     = S.singleton a
  variables Const{}       = S.empty
  variables (App l r)     = variables l `S.union` variables r
  variables (Lam a _ bdy) = S.singleton a `S.union` variables bdy

  -- |Collects the free variables (i.e. variables appearing within a
  --  term not bound by a lambda-abstraction) into a Set.
  fv :: Term -> S.Set String
  fv (Var a _)     = S.singleton a
  fv (Const _)     = S.empty
  fv (App l r)     = fv l `S.union` fv r
  fv (Lam a _ bdy) = a `S.delete` fv bdy

  -- |Collects the type variables appearing anywhere within a term
  --  into a Set.  Lambda abstractions, constants and term variables
  --  are all decorated with types.  This function collects the type
  --  variables of those types into a Set.
  typeVars :: Term -> S.Set String
  typeVars (Var _ ty)     = tv ty
  typeVars (Const d)      = tv . constantDescriptionType $ d
  typeVars (App l r)      = typeVars l `S.union` typeVars r
  typeVars (Lam _ ty bdy) = tv ty `S.union` typeVars bdy

  -- |Collects the free variables of a list of terms into a Set.
  fvs :: (F.Foldable f, Functor f) => f Term -> S.Set String
  fvs ts = F.foldr S.union S.empty $ fmap fv ts

  -- |Performs a swapping of names within terms.  Used to define
  --  alpha-equivalence later.
  permute :: String -> String -> Term -> Term
  permute a b (Var c ty)
    | a == c    = Var b ty
    | b == c    = Var a ty
    | otherwise = Var c ty
  permute _ _ (Const d) = Const d
  permute a b (App l r) = App (permute a b l) $ permute a b r
  permute a b (Lam c ty body)
    | a == c    = Lam b ty $ permute a b body
    | b == c    = Lam a ty $ permute a b body
    | otherwise = Lam c ty $ permute a b body

  instance Eq Term where
    (Var a ty)     == (Var b ty')      = a == b && ty == ty'
    (Const c)      == (Const d)        = c == d
    (App l r)      == (App m s)        = l == m && r == s
    (Lam a ty bdy) == (Lam b ty' bdy')
      | a == b    = ty == ty' && bdy == bdy'
      | otherwise =
        if a `S.member` fv bdy' then
          False
        else
          bdy == permute a b bdy' && ty == ty'
    _ == _ = False

  -- |Structural equality wrapper for terms so that we have both alpha-equivalence
  --  on terms (using the Eq type class on raw terms) and a structural equality
  --  (using the Eq type class on StructuralEquality).
  newtype StructuralEquality = StructuralEquality { getTerm :: Term }

  -- |Create a new StructuralEquality wrapper from a term.
  mkStructuralEquality :: Term -> StructuralEquality
  mkStructuralEquality = StructuralEquality

  instance Eq StructuralEquality where
    s == s' = go (getTerm s) (getTerm s')
      where
        go :: Term -> Term -> Bool
        go (Var a ty)     (Var b ty')      = a == b && ty == ty'
        go (Const c)      (Const d)        = c == d
        go (App l r)      (App m q)        =
          and [
            mkStructuralEquality l == mkStructuralEquality m
          , mkStructuralEquality r == mkStructuralEquality q
          ]
        go (Lam a ty bdy) (Lam b ty' bdy') =
          and [
            a == b
          , ty == ty'
          , mkStructuralEquality bdy == mkStructuralEquality bdy'
          ]
        go _ _ = False
  --
  -- * Pretty printing terms.
  --

  instance Size Term where
    size Var{}         = 1
    size Const{}       = 1
    size (App l r)     = 1 + size l + size r
    size (Lam _ _ bdy) = 1 + size bdy

  -- TODO: print mixfix syntax correctly like for types.
  instance Pretty Term where
    pretty (Var a _)     = a
    pretty (Const d)      = pretty d
    pretty (App (App (Const d) c) r)
      -- XXX: this needs properly fixing for arbitrary mixfix syntax
      | isInfix . constantDescriptionQualifiedName $ d = unwords [bracket c, pretty d, bracket r]
      | otherwise = bracket (App (Const d) c) ++ " " ++ bracket r
    pretty (App (App l c) r) = unwords . map bracket $ [l, c, r]
    pretty (App l r)      = unwords [bracket l, bracket r]
    pretty (Lam a _ bdy) =
      "λ" ++ a ++ ". " ++ bracket bdy

  --
  -- * HOL theorems
  -- 

  -- |A provenance tag for theorems.  Indelibly marks axioms
  --  with a @FromAxiom@ tag.  Everything that is not introduced
  --  as an axiom via the @primitiveNewAxiom@ function is said
  --  to be derived safely.
  data Provenance
    = FromAxiom
    | DerivedSafely
    deriving (Eq, Show, Ord)

  -- |Takes two provenance tags and produces a new one.  If either
  --  of the tags provided as input are @FromAxiom@ then the output
  --  will also be @FromAxiom@, otherwise will be @DerivedSafely@.
  --  Used to update provenance information in the primitive
  --  inference rules of the Mosquito logic provided below.
  track :: Provenance -> Provenance -> Provenance
  FromAxiom     `track` _             = FromAxiom
  _             `track` FromAxiom     = FromAxiom
  DerivedSafely `track` DerivedSafely = DerivedSafely

  instance Pretty Provenance where
    pretty FromAxiom     = "\t[✘]"
    pretty DerivedSafely = "\t[✔]"

  -- |A theorem consists of a provenance tag detailing how it was
  --  derived (or more accurately, if any axiom was ever used in
  --  the derivation) combined with a list of hypotheses and a single
  --  conclusion.  All terms making up the hypotheses and conclusion
  --  must be boolean-typed.
  data Theorem = Theorem Provenance ([Term], Term)
    deriving(Show, Eq, Ord)

  -- |Obtain the hypotheses of a theorem.
  hypotheses :: Theorem -> [Term]
  hypotheses (Theorem _ (hyps, _)) = hyps

  -- |Obtain the conclusion of a theorem.
  conclusion :: Theorem -> Term
  conclusion (Theorem _ (_, concl)) = concl

  -- |Obtain the provenance flag of a theorem.
  provenance :: Theorem -> Provenance
  provenance (Theorem p _) = p

  -- |Alpha-equivalent aware set-like union of term lists.
  union :: [Term] -> [Term] -> [Term]
  union = L.unionBy (==)

  -- |Alpha-equivalent aware set-like delete of term lists.
  delete :: Term -> [Term] -> [Term]
  delete = L.deleteBy (==)

  deleteTheorem :: Term -> [Theorem] -> [Theorem]
  deleteTheorem _ [] = []
  deleteTheorem t (Theorem p ([], concl):xs)
    | t == concl = deleteTheorem t xs
    | otherwise  = Theorem p ([], concl):deleteTheorem t xs
  deleteTheorem t (x:xs) = x:deleteTheorem t xs

  --
  -- ** Pretty printing theorems
  --

  instance Pretty Theorem where
    pretty (Theorem p ([], concl)) =
      unwords [
        "⊢"
      , pretty concl
      , pretty p
      ]
    pretty (Theorem p (hyps, concl)) =
      unwords [
        L.intercalate ",\n" $ map pretty hyps
      , "⊢"
      , pretty concl
      , pretty p
      ]

  --
  -- ** The basic HOL theorems
  --

  -- |Produces a derivation of @{} ⊢ t = t'@ given two terms @t@ and @t'@
  --  that are alpha-equivalent.
  alpha :: Term -> Term -> Inference Theorem
  alpha t u = do
    kernelMark ["alpha:", pretty t, pretty u]
    if t == u then do
      eq     <- mkEquality t u
      return $  Theorem DerivedSafely ([], eq)
    else
      fail . unwords $ [
        "alpha: Input terms to `reflexivity' are not alpha-equivalent."
      , unwords ["Was expecting `", pretty t, "' to be alpha-equivalent"]
      , unwords ["with `", pretty u, "'."]
      ]

  -- |Produces a derivation of @Gamma ⊢ s = t@ given a derivation of
  --  @Gamma ⊢ t = s@.  Note, not strictly necessary to have this in
  --  the kernel.
  symmetry :: Theorem -> Inference Theorem
  symmetry (Theorem p (hyps, concl)) = do
    kernelMark ["symmetry:", pretty concl]
    (left, right) <- fromEquality concl
    eq            <- mkEquality right left
    return $ Theorem p (hyps, eq)

  -- |Produces a derivation of @Gamma u Delta ⊢ t = v@ given a derivation of
  --  @Gamma ⊢ t = s@ and @Delta ⊢ s = u@ for all t, u and v.
  transitivity :: Theorem -> Theorem -> Inference Theorem
  transitivity (Theorem p (hyps, concl)) (Theorem q (hyps', concl')) = do
    kernelMark ["transitivity:", pretty concl, pretty concl']
    (left, right)   <- fromEquality concl
    (left', right') <- fromEquality concl'
    if mkStructuralEquality right == mkStructuralEquality left' then do
      eq              <- mkEquality left right'
      return $ Theorem (p `track` q) (hyps `union` hyps', eq)
    else
      fail . unwords $ [
        "transitivity: The two derivations supplied to `transitivity' are not valid",
        "arguments as terms are not structurally equivalent.  Was expecting",
        "term `" ++ pretty right ++ "' to be structurally-equivalent with",
        "term `" ++ pretty left' ++ "'."
      ]

  -- |Produces a derivation @{p} ⊢ p@ for @p@ a term of type @Bool@.
  assume :: Term -> Inference Theorem
  assume t = do
    kernelMark ["assume:", pretty t]
    typeOfT <- typeOf t
    if typeOfT == boolType then
      return $ Theorem DerivedSafely ([t], t)
    else
      fail . unwords $ [
        "assume: Term given to `assume' is not a formula, but has type"
      , unwords ["`", pretty typeOfT, "'."]
      ]

  -- |Produces a derivation of @(Gamma - q) u (Delta - p) ⊢ p = q@ from a pair of
  --  derivations of @Gamma ⊢ p@ and @Delta ⊢ q@.
  deductAntiSymmetric :: Theorem -> Theorem -> Inference Theorem
  deductAntiSymmetric (Theorem p (hyps, concl)) (Theorem q (hyps', concl')) = do
    kernelMark ["deductAntiSymmetric:", pretty concl, pretty concl']
    eq <- mkEquality concl concl'
    let hyps'' = (delete concl hyps') `union` (delete concl' hyps)
    return $ Theorem (p `track` q) (hyps'', eq)

  -- |Produces a derivation of @Gamma ⊢ λx:ty. t = λx:ty. u@ given a derivation
  -- of the form @Gamma ⊢ t = u@.
  abstract :: String -> Type -> Theorem -> Inference Theorem
  abstract name ty (Theorem p (hyps, concl)) = do
    kernelMark ["abstract:", name, pretty ty, pretty concl]
    if not $ name `S.member` fvs hyps then do
      (left, right) <- fromEquality concl
      eq            <- mkEquality (mkLam name ty left) (mkLam name ty right)
      return $ Theorem p (hyps, eq)
    else
      fail . unwords $ [
        "abstract: Supplied name for lambda-abstraction to `abstract' appears free",
        "in hypotheses of supplied theorem: `" ++ name ++ "'."
      ]

  -- |Produces a derivation of @Gamma u Delta ⊢ q@ given two derivations of
  --  @Gamma ⊢ p = q@ and @Delta ⊢ p@ respectively.
  equalityModusPonens :: Theorem -> Theorem -> Inference Theorem
  equalityModusPonens (Theorem p (hyps, concl)) (Theorem q (hyps', concl')) = do
    kernelMark ["equalityModusPonens:", pretty concl, pretty concl']
    (left, right) <- fromEquality concl
    if concl' == left
      then
        return $ Theorem (p `track` q) (hyps `union` hyps', right)
      else
        fail . unwords $ [
          "equalityModusPonens: Conclusion of second theorem supplied to `equalityModusPonens' is",
          "not alpha-equivalent to the left-hand side of the equality in the",
          "conclusion of the first theorem. Was expecting term alpha-equivalent",
          "to: `" ++ pretty left ++ "' but found: `" ++ pretty concl' ++ "'."
        ]

  -- |Produces a derivation of @Gamma u Delta ⊢ f x = g y@ given two derivations
  --  of the form @Gamma ⊢ f = g@ and @Delta ⊢ x = y@.
  combine :: Theorem -> Theorem -> Inference Theorem
  combine (Theorem p (hyps, concl)) (Theorem q (hyps', concl')) = do
    kernelMark ["combine:", pretty concl, pretty concl']
    (f, g) <- fromEquality concl
    (x, y) <- fromEquality concl'
    left   <- mkApp f x
    right  <- mkApp g y
    eq     <- mkEquality left right
    return $ Theorem (p `track` q) (hyps `union` hyps', eq)

  -- |Produces a derivation @{} ⊢ (λx:ty. t)u = t[x := u]@ given an application.
  --  Note that this derivation rule is stronger than its HOL-light counterpart,
  --  as we permit full beta-equivalence in the kernel via this rule.
  beta :: Term -> Inference Theorem
  beta t@(App (Lam name _ body) b) = do
    kernelMark ["beta:", pretty t]
    eq   <- mkEquality t $ termSubst name b body
    return $ Theorem DerivedSafely ([], eq)
  beta t =
    fail . unwords $ [
      "beta: Cannot apply `beta' as term passed to function is not a valid",
      "beta-redex, in term: `" ++ pretty t ++ "'."
    ]

  -- |Produces a derivation of @{} ⊢ λx:ty. (t x) = t@ when @x@ is not in the
  --  free variables of @t@.  Note that unlike HOL-light we take this as a
  --  primitive inference rule in the kernel, as opposed to taking it as an
  --  axiom later.
  eta :: Term -> Inference Theorem
  eta t@(Lam name _ (App left (Var v _)))
    | v == name = do
        kernelMark ["eta:", pretty t]
        if not $ v `S.member` fv left then do
          eq <- mkEquality t left
          return $ Theorem DerivedSafely ([], eq)
        else
          fail . unwords $ [
            unwords ["eta: Cannot apply `eta' as variable `", name, "' appears free"]
          , unwords ["in body of lambda abstraction `", pretty left, "'."]
          ]
    | otherwise =
        fail . unwords $ [
          "eta: Input term is not of correct shape to apply `eta':"
        , unwords ["`", pretty t, "'."]
        ]
  eta t =
    fail . unwords $ [
      "eta: Cannot apply `eta' as term passed to function is not a valid"
    , unwords ["eta-redex, in term: `", pretty t, "'."]
    ]

  typeInstantiation :: String -> Type -> Theorem -> Inference Theorem
  typeInstantiation dom rng (Theorem p (hyps, concl)) = do
    kernelMark ["typeInstantiation:", dom, pretty rng, pretty concl]
    return $ Theorem p (map (termTypeSubst dom rng) hyps, termTypeSubst dom rng concl)

  instantiation :: String -> Term -> Theorem -> Inference Theorem
  instantiation dom rng (Theorem p (hyps, concl)) = do
    kernelMark ["instantiation:", dom, pretty rng, pretty concl]
    return $ Theorem p (map (termSubst dom rng) hyps, termSubst dom rng concl)

  --
  -- * Extending the logic
  --

  primitiveNewDefinedConstant :: QualifiedName -> Term -> Type -> Inference (Term, Theorem)
  primitiveNewDefinedConstant name t typ =
    if fv t == S.empty then
      if typeVars t `S.isSubsetOf` tv typ then do
        let defined = mkConst $ DefinedConstant name typ t
        eq <- mkEquality defined t
        return (defined, Theorem DerivedSafely ([], eq))
      else
        fail . unwords $ [
          "primitiveNewDefinedConstant: Free type variables of definiens supplied to `primitiveNewDefinedConstant'"
        , "is not a subset of the free type variables of the type of the"
        , unwords ["left hand side, in term: `", pretty t, "'."]
        ]
    else
      fail . unwords $ [
        "primitiveNewDefinedConstant: Definiens supplied to `primitiveNewDefinedConstant' has free variables, in"
      , unwords ["term: `", pretty t, "'."]
      ]

  primitiveNewAxiom :: Term -> Inference Theorem
  primitiveNewAxiom term = do
    typeOfTerm <- typeOf term
    if typeOfTerm == boolType then
      return $ Theorem FromAxiom ([], term)
    else
      fail . unwords $ [
        unwords ["primitiveNewAxiom: Term `", pretty term, "' passed to `newAxiom' is not"]
      , unwords ["a proposition, instead having type `", pretty typeOfTerm, "'."]
      ]