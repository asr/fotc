{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Functors where

-- The carrier of the initial algebra is (up to isomorphism) a
-- fixed-point of the functor (Vene 2000, p).

-- • Varmo Vene. Categorical programming with inductive and
--   coinductive types. PhD thesis, University of Taru, Estonia, 2000.

------------------------------------------------------------------------------

data Bool : Set where
  false true : Bool

data _⊎_  (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- The terminal object.
data One : Set where
   one : One

postulate
  -- The least fixed-point.
  -- The names came from the Haskell definitions

  -- data Mu f = In (f (Mu f))

  -- unIn :: Mu f → f (Mu f)
  -- unIn (In x) = x

  Mu   : (Set → Set) → Set
  In   : {f : Set → Set} → f (Mu f) → Mu f
  unIn : {f : Set → Set} → Mu f → f (Mu f)

postulate
  -- The greatest fixed-point.
  -- The names came from the Haskell definitions

  -- data Nu f = Wrap (f (Nu f))

  -- out :: Nu f → (f (Nu f))
  -- out (Wrap x) = x

  Nu   : (Set → Set) → Set
  Wrap : {f : Set → Set} → f (Nu f) → Nu f
  out  : {f : Set → Set} → Nu f → f (Nu f)

------------------------------------------------------------------------------
-- Functors

--  The identity functor (the functor for the empty and unit types).
IdF : Set → Set
IdF X = X

-- The (co)natural numbers functor.
NatF : Set → Set
NatF X = One ⊎ X

-- The (co)list functor.
ListF : Set → Set → Set
ListF A X = One ⊎ (A × X)

-- The stream functor.
StreamF : Set → Set → Set
StreamF A X = A × X

------------------------------------------------------------------------------
-- Types as least fixed-points

-- The empty type is a least fixed-point.
⊥ : Set
⊥ = Mu IdF

-- The natural numbers type is a least fixed-point.
N : Set
N = Mu NatF

-- The data constructors for the natural numbers.
zero : N
zero = In (inl one)

succ : N → N
succ n = In (inr n)

-- The list type is a least fixed-point.
List : Set → Set
List A = Mu (ListF A)

-- The data constructors for List.
nil : {A : Set} → List A
nil = In (inl one)

cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))

------------------------------------------------------------------------------
-- Types as greatest fixed-points

-- The unit type is a greatest fixed-point.
Unit : Set
Unit = Nu IdF

-- Non-structural recursion
-- unit : Nu IdF
-- unit = Wrap IdF {!unit!}

-- The conaturals type is a greatest fixed-point.
Conat : Set
Conat = Nu NatF

zeroC : Conat
zeroC = Wrap (inl one)

succC : Conat → Conat
succC cn = Wrap (inr cn)

-- Non-structural recursion for the definition of ∞C.
-- ∞C : Conat
-- ∞C = succC {!∞C!}

-- TODO: The conat destructor.
pred : Conat → One ⊎ Conat
pred cn with out cn
... | inl _ = inl one
... | inr x = inr x

-- The colist type is a greatest fixed-point.
Colist : Set → Set
Colist A = Nu (ListF A)

-- The colist data constructors.
nilCL : {A : Set} → Colist A
nilCL = Wrap (inl one)

consCL : {A : Set} → A → Colist A → Colist A
consCL x xs = Wrap (inr (x , xs))

-- The colist destructors.
nullCL : {A : Set} → Colist A → Bool
nullCL xs with out xs
... | inl _ = true
... | inr _ = false

-- headCL : {A : Set} → Colist A → A
-- headCL {A} xs with out (ListF A) xs
-- ... | inl t       =  -- Impossible
-- ... | inr (x , _) = x

-- tailCL : {A : Set} → Colist A → Colist A
-- tailCL {A} xs with out (ListF A) xs
-- ... | inl t         =  -- Impossible
-- ... | inr (_ , xs') = xs'

-- The stream type is a greatest fixed-point.
Stream : Set → Set
Stream A = Nu (StreamF A)

-- The stream data constructor.
consS : {A : Set} → A → Stream A → Stream A
consS x xs = Wrap (x , xs)

-- The stream destructors.
headS : {A : Set} → Stream A → A
headS xs with out xs
... | x , _ = x

tailS : {A : Set} → Stream A → Stream A
tailS xs with out xs
... | _ , xs' = xs'
