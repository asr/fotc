{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module ConatSL where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Coinduction

------------------------------------------------------------------------------

data Coℕ : Set where
  zero : Coℕ
  succ : ∞ Coℕ → Coℕ

-- Adapted from (Leclerc and Paulin-Mohring 1994, p. 195).
Coℕ-build : {A : Set} → (A → ⊤ ⊎ A) → A → Coℕ
Coℕ-build h a with h a
... | inj₁ tt = zero
... | inj₂ a' = succ (♯ (Coℕ-build h a'))

-- Adapted from Coℕ-build.
Coℕ-coind : (A : Coℕ → Set) →
            (∀ {n} → A n → ⊤ ⊎ A (succ (♯ n))) →
            ∀ {n} → A n → Coℕ
Coℕ-coind A h An with h An
... | inj₁ tt  = zero
... | inj₂ An' = succ (♯ (Coℕ-coind A h An'))

-- TODO (07 January 2014): Is it proof correct?
Coℕ-stronger-coind : ∀ (A : Coℕ → Set) {n} →
                     (A n → ⊤ ⊎ A (succ (♯ n))) →
                     A n → Coℕ
Coℕ-stronger-coind A h An with h An
... | inj₁ tt  = zero
... | inj₂ An' = succ (♯ (Coℕ-stronger-coind A h An))

------------------------------------------------------------------------------
-- References
--
-- Leclerc, F. and Paulin-Mohring, C. (1994). Programming with Streams
-- in Coq. A case study : the Sieve of Eratosthenes. In: Types for
-- Proofs and Programs (TYPES ’93). Ed. by Barendregt, H. and Nipkow,
-- T. Vol. 806. LNCS. Springer, pp. 191–212.
