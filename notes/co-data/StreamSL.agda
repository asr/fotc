------------------------------------------------------------------------------
-- Testing the co-induction principle for streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module StreamSL where

open import Data.Nat
open import Coinduction

------------------------------------------------------------------------------

infixr 5 _∷_

data Streamℕ : Set where
  _∷_ : ℕ → ∞ Streamℕ → Streamℕ

-- From
-- https://groups.google.com/forum/#!topic/homotopytypetheory/Ev-9i2Va4_Q.
--
-- TODO (26 December 2013): We aren't using the function A → A.
Streamℕ-coind : {A : Set} → (A → ℕ) → (A → A) → A → Streamℕ
Streamℕ-coind f g a = f a ∷ ♯ (Streamℕ-coind f g a)
