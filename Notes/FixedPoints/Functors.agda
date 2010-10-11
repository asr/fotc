-- Tested with Agda 2.2.9 from 11 October 2010.

module Functors where

-- The carrier of the initial algebra is (up to isomorphism) a
-- fixed-point of the functor [1, p. 18].

-- [1] Varmo Vene. Categorical programming with inductive and
-- coinductive types. PhD thesis, University of Taru, Estonia, 2000.

------------------------------------------------------------------------------

data _⊎_  (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- The terminal object.
data I : Set where
  t : I

postulate
  lfp   : (Set → Set) → Set
  cLFP₁ : (f : Set → Set) → lfp f → f (lfp f)
  cLFP₂ : (f : Set → Set) → f (lfp f) → lfp f

  gfp   : (Set → Set) → Set
  cGFP₁ : (f : Set → Set) → gfp f → f (gfp f)
  cGFP₂ : (f : Set → Set) → f (gfp f) → gfp f

------------------------------------------------------------------------------

-- The empty functor (the identity functor).
FE : Set → Set
FE X = X

-- The empty type is a least fixed-point.
⊥ : Set
⊥ = lfp FE

------------------------------------------------------------------------------

-- The natural numbers functor.
FN : Set → Set
FN X = I ⊎ X

-- The natural numbers type is a least fixed-point.
N : Set
N = lfp FN

-- The data constructors for the natural numbers.
zero : N
zero = cLFP₂ FN (inl t)

succ : N → N
succ n = cLFP₂ FN (inr n)

------------------------------------------------------------------------------

-- The list functor.
FL : Set → Set → Set
FL A X = I ⊎ (A × X)

-- The list type is a least fixed-point.
List : Set → Set
List A = lfp (FL A)

-- The data constructors for List.
nil : (A : Set) → List A
nil A = cLFP₂ (FL A) (inl t)

cons : (A : Set) → A → List A → List A
cons A x xs = cLFP₂ (FL A) (inr (x , xs))

------------------------------------------------------------------------------

-- The conaturals type is a greatest fixed-point.
Conat : Set
Conat = gfp FN

-- TODO: The conat destructor.
pred : Conat → I ⊎ Conat
pred cn with cGFP₁ FN cn
... | inl t = inl t
... | inr x = inr x

------------------------------------------------------------------------------

-- The stream functor.
FS : Set → Set → Set
FS A X = A × X

-- The stream type is a greatest fixed-point.
Stream : Set → Set
Stream A = gfp (FS A)

-- The stream destructors.
head : (A : Set) → Stream A → A
head A xs with cGFP₁ (FS A) xs
... | x , _ = x

tail : (A : Set) → Stream A → Stream A
tail A xs with cGFP₁ (FS A) xs
... | _ , xs' = xs'
