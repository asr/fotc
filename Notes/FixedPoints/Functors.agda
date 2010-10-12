-- Tested with Agda 2.2.9 from 11 October 2010.

module Functors where

-- The carrier of the initial algebra is (up to isomorphism) a
-- fixed-point of the functor [1, p. 18].

-- [1] Varmo Vene. Categorical programming with inductive and
-- coinductive types. PhD thesis, University of Taru, Estonia, 2000.

------------------------------------------------------------------------------

data Bool : Set where
  false true : Bool

data _⊎_  (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- The terminal object.
data I : Set where
  to : I

postulate
  -- The least fixed-point.
  -- The names came from the Haskell definition

  -- data Mu f = In (f (Mu f))

  -- unIn :: Mu f → f (Mu f)
  -- unIn (In x) = x

  Mu   : (Set → Set) → Set
  In   : {f : Set → Set} → f (Mu f) → Mu f
  unIn : {f : Set → Set} → Mu f → f (Mu f)

postulate
  -- The greatest fixed-point.
  -- The names came from the Haskell definition

  -- data Nu f = Wrap (f (Nu f))

  -- out :: Nu f → (f (Nu f))
  -- out (Wrap x) = x

  Nu   : (Set → Set) → Set
  Wrap : {f : Set → Set} → f (Nu f) → Nu f
  out  : {f : Set → Set} → Nu f → f (Nu f)

------------------------------------------------------------------------------
-- Functors

--  The identity functor (the functor for the empty and unit types).
FId : Set → Set
FId X = X

-- The (co)natural numbers functor.
FN : Set → Set
FN X = I ⊎ X

-- The (co)list functor.
FL : Set → Set → Set
FL A X = I ⊎ (A × X)

-- The stream functor.
FS : Set → Set → Set
FS A X = A × X

------------------------------------------------------------------------------
-- Types as least fixed-points

-- The empty type is a least fixed-point.
⊥ : Set
⊥ = Mu FId

-- The natural numbers type is a least fixed-point.
N : Set
N = Mu FN

-- The data constructors for the natural numbers.
zero : N
zero = In (inl to)

succ : N → N
succ n = In (inr n)

-- The list type is a least fixed-point.
List : Set → Set
List A = Mu (FL A)

-- The data constructors for List.
nil : (A : Set) → List A
nil A = In (inl to)

cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))

------------------------------------------------------------------------------
-- Types as greatest fixed-points

-- The unit type is a greatest fixed-point.
Unit : Set
Unit = Nu FId

-- Non-structural recursion
-- unit : Nu FId
-- unit = Wrap FId {!unit!}

-- The conaturals type is a greatest fixed-point.
Conat : Set
Conat = Nu FN

-- TODO: The conat destructor.
pred : Conat → I ⊎ Conat
pred cn with out cn
... | inl t = inl t
... | inr x = inr x

-- The colist type is a greatest fixed-point.
Colist : Set → Set
Colist A = Nu (FL A)

-- The colist destructors.
nullCL : {A : Set} → Colist A → Bool
nullCL xs with out xs
... | inl t = true
... | inr _ = false

-- headCL : {A : Set} → Colist A → A
-- headCL {A} xs with out (FL A) xs
-- ... | inl t       =  -- Impossible
-- ... | inr (x , _) = x

-- tailCL : {A : Set} → Colist A → Colist A
-- tailCL {A} xs with out (FL A) xs
-- ... | inl t         =  -- Impossible
-- ... | inr (_ , xs') = xs'

-- The stream type is a greatest fixed-point.
Stream : Set → Set
Stream A = Nu (FS A)

-- The stream destructors.
headS : {A : Set} → Stream A → A
headS xs with out xs
... | x , _ = x

tailS : {A : Set} → Stream A → Stream A
tailS xs with out xs
... | _ , xs' = xs'
