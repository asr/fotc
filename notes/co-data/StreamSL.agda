------------------------------------------------------------------------------
-- Testing the co-induction principle for streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module StreamSL where

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Coinduction

------------------------------------------------------------------------------

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : A → ∞ (Stream A) → Stream A

-- Adapted from (Leclerc and Paulin-Mohring 1994, p. 195).
Stream-build : {A X : Set} → (X → A × X) → X → Stream A
Stream-build h x with h x
... | a , x' = a ∷ ♯ (Stream-build h x')

-- From (Giménez, 1995, p. 40).
Stream-corec : {A X : Set} → (X → A × (Stream A ⊎ X)) → X → Stream A
Stream-corec h x with h x
... | a , inj₁ xs = a ∷ ♯ xs
... | a , inj₂ x' = a ∷ ♯ (Stream-corec h x')

------------------------------------------------------------------------------

data Streamℕ : Set where
  _∷_ : ℕ → ∞ Streamℕ → Streamℕ

-- From
-- https://groups.google.com/forum/#!topic/homotopytypetheory/Ev-9i2Va4_Q.
--
-- TODO (26 December 2013): We aren't using the function A → A.
Streamℕ-coind : {A : Set} → (A → ℕ) → (A → A) → A → Streamℕ
Streamℕ-coind f g a = f a ∷ ♯ (Streamℕ-coind f g a)

------------------------------------------------------------------------------
-- References
--
-- Giménez, E. (1995). Codifying guarded deﬁnitions with recursive
-- schemes. In: Types for Proofs and Programs (TYPES ’94). Ed. by
-- Dybjer, P., Nordström, B. and Smith, J. Vol. 996. LNCS. Springer,
-- pp. 39–59.
--
-- Leclerc, F. and Paulin-Mohring, C. (1994). Programming with Streams
-- in Coq. A case study : the Sieve of Eratosthenes. In: Types for
-- Proofs and Programs (TYPES ’93). Ed. by Barendregt, H. and Nipkow,
-- T. Vol. 806. LNCS. Springer, pp. 191–212.
