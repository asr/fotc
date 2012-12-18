------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.Properties.UnprovedATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

helper : ∀ {n} → N n → collatz ([2] ^ succ₁ n) ≡ collatz ([2] ^ n)
helper nzero = prf
  where postulate prf : collatz ([2] ^ succ₁ zero) ≡ collatz ([2] ^ zero)
helper (nsucc {n} Nn) = prf
  -- 18 December 2012: The ATPs could not prove the theorem (240 sec).
  where postulate prf : collatz ([2] ^ succ₁ (succ₁ n)) ≡ collatz ([2] ^ succ₁ n)
        {-# ATP prove prf +∸2 ^-N 2-N 2^x≢0 2^[x+1]≢1 div-2^[x+1]-2≡2^x
                      x-Even→SSx-Even ∸-N ∸-Even 2^[x+1]-Even 2-Even
         #-}
