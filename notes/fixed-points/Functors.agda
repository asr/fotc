{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Based on (Vene, 2000).

module Functors where

infixr 1 _+_
infixr 2 _×_

data Bool : Set where
  false true : Bool

data _+_  (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- The terminal object.
data ⊤ : Set where
   <> : ⊤

postulate
  -- The least fixed-point.

  -- Haskell definitions:

  -- data Mu f = In (f (Mu f))

  -- unIn :: Mu f → f (Mu f)
  -- unIn (In x) = x

  μ    : (Set → Set) → Set
  In   : {F : Set → Set} → F (μ F) → μ F
  unIn : {F : Set → Set} → μ F → F (μ F)

postulate
  -- The greatest fixed-point.

  -- Haskell definitions:

  -- data Nu f = Wrap (f (Nu f))

  -- out :: Nu f → (f (Nu f))
  -- out (Wrap x) = x

  ν    : (Set → Set) → Set
  Wrap : {F : Set → Set} → F (ν F) → ν F
  out  : {F : Set → Set} → ν F → F (ν F)

------------------------------------------------------------------------------
-- Functors

--  The identity functor (the functor for the empty and unit types).
IdF : Set → Set
IdF X = X

-- The (co)natural numbers functor.
NatF : Set → Set
NatF X = ⊤ + X

-- The (co)list functor.
ListF : Set → Set → Set
ListF A X = ⊤ + A × X

-- The stream functor.
StreamF : Set → Set → Set
StreamF A X = A × X

------------------------------------------------------------------------------
-- Types as least fixed-points

-- The empty type is a least fixed-point.
⊥ : Set
⊥ = μ IdF

-- The natural numbers type is a least fixed-point.
N : Set
N = μ NatF

-- The data constructors for the natural numbers.
zero : N
zero = In (inl <>)

succ : N → N
succ n = In (inr n)

-- The list type is a least fixed-point.
List : Set → Set
List A = μ (ListF A)

-- The data constructors for List.
nil : {A : Set} → List A
nil = In (inl <>)

cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))

------------------------------------------------------------------------------
-- Types as greatest fixed-points

-- The unit type is a greatest fixed-point.
Unit : Set
Unit = ν IdF

-- Non-structural recursion
-- unit : Nu IdF
-- unit = Wrap IdF {!unit!}

-- The conat type is a greatest fixed-point.
Conat : Set
Conat = ν NatF

zeroC : Conat
zeroC = Wrap (inl <>)

succC : Conat → Conat
succC cn = Wrap (inr cn)

-- Non-structural recursion for the definition of ∞C.
-- ∞C : Conat
-- ∞C = succC {!∞C!}

-- The pred function is the conat destructor.
pred : Conat → ⊤ + Conat
pred cn with out cn
... | inl _ = inl <>
... | inr x = inr x

-- The colist type is a greatest fixed-point.
Colist : Set → Set
Colist A = ν (ListF A)

-- The colist data constructors.
nilCL : {A : Set} → Colist A
nilCL = Wrap (inl <>)

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
Stream A = ν (StreamF A)

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

-- From (Leclerc and Paulin-Mohring 1994, p. 195).
--
-- TODO (07 January 2014): Agda doesn't accept the definition of
-- Stream-build.
{-# NO_TERMINATION_CHECK #-}
Stream-build :
  {A X : Set} →
  (X → StreamF A X) →
  X → Stream A
Stream-build f x with f x
... | a , x' = Wrap (a , Stream-build f x')

------------------------------------------------------------------------------
-- References
--
-- Leclerc, F. and Paulin-Mohring, C. (1994). Programming with Streams
-- in Coq. A case study : the Sieve of Eratosthenes. In: Types for
-- Proofs and Programs (TYPES ’93). Ed. by Barendregt, H. and Nipkow,
-- T. Vol. 806. LNCS. Springer, pp. 191–212.
--
-- Vene, Varmo (2000). Categorical programming with inductive and
-- coinductive types. PhD thesis. Faculty of Mathematics: University
-- of Tartu.
