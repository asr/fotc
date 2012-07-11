------------------------------------------------------------------------------
-- Testing the conversion from/to natural numbers to/from co-natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.PropertiesSL where

open import Coinduction
open import Data.Conat renaming ( suc to csuc )
open import Data.Nat

------------------------------------------------------------------------------

ℕ→Coℕ : ℕ → Coℕ
ℕ→Coℕ zero    = zero
ℕ→Coℕ (suc n) = csuc (♯ (ℕ→Coℕ n))

{-# NO_TERMINATION_CHECK #-}
Coℕ→ℕ : Coℕ → ℕ
Coℕ→ℕ zero     = zero
Coℕ→ℕ (csuc n) = suc (Coℕ→ℕ (♭ n))
