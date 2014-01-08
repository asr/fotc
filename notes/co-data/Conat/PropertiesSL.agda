------------------------------------------------------------------------------
-- Conat properties using the standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Conat.PropertiesSL where

open import Coinduction
open import Data.Conat
open import Data.Nat

------------------------------------------------------------------------------

ℕ→Coℕ : ℕ → Coℕ
ℕ→Coℕ zero    = zero
ℕ→Coℕ (suc n) = suc (♯ (ℕ→Coℕ n))

{-# NO_TERMINATION_CHECK #-}
Coℕ→ℕ : Coℕ → ℕ
Coℕ→ℕ zero     = zero
Coℕ→ℕ (suc n) = suc (Coℕ→ℕ (♭ n))
