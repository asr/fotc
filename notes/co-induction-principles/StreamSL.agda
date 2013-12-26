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
  _∷_ : (x : ℕ) (xs : ∞ (Streamℕ)) → Streamℕ

-- 26 December 2013. From
-- https://groups.google.com/forum/#!topic/homotopytypetheory/Ev-9i2Va4_Q.
Stream-coind : {A : Set} → (A → ℕ) → (A → A) → A → Streamℕ
Stream-coind f g a = f a ∷ ♯ (Stream-coind f g a)
