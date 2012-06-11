------------------------------------------------------------------------------
-- Testing the conversion from/to natural numbers to/from co-natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 11 June 2012.

module PropertiesSL where

open import Coinduction
open import Data.Conat renaming ( suc to csuc )
open import Data.Nat

------------------------------------------------------------------------------

ℕ→Coℕ : ℕ → Coℕ
ℕ→Coℕ zero    = zero
ℕ→Coℕ (suc n) = csuc (♯ (ℕ→Coℕ n))

Coℕ→ℕ : Coℕ → ℕ
Coℕ→ℕ zero     = zero
Coℕ→ℕ (csuc n) = suc (Coℕ→ℕ (♭ n))
