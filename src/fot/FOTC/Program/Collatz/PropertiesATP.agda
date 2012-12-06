------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.ConversionRulesATP
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

helper-helper : ∀ {n} → N n → collatz ([2] ^ succ₁ n) ≡
                        collatz (div ([2] ^ succ₁ n) [2])
helper-helper nzero = prf
  where postulate prf : collatz ([2] ^ succ₁ zero) ≡
                        collatz (div ([2] ^ succ₁ zero) [2])
        {-# ATP prove prf #-}

helper-helper (nsucc {n} Nn) = prf
  where postulate prf : collatz ([2] ^ succ₁ (succ₁ n)) ≡
                        collatz (div ([2] ^ succ₁ (succ₁ n)) [2])
        {-# ATP prove prf +∸2 ^-N 2-N 2^x≢0 2^[x+1]≢1
                      collatz-even x-Even→SSx-Even ∸-N ∸-Even 2^[x+1]-Even
                      2-Even
        #-}

-- We help the ATPs proving the helper-helper property first.
postulate helper : ∀ {n} → N n → collatz ([2] ^ succ₁ n) ≡ collatz ([2] ^ n)
{-# ATP prove helper helper-helper div-2^[x+1]-2≡2^x #-}

collatz-2^x : ∀ {n} → N n → (∃[ k ] N k ∧ n ≡ [2] ^ k) → collatz n ≡ [1]
collatz-2^x {n} Nn (.zero , nzero , h) = prf
  where postulate prf : collatz n ≡ [1]
        {-# ATP prove prf #-}

collatz-2^x {n} Nn (.(succ₁ k) , nsucc {k} Nk , h) =
  prf (collatz-2^x (^-N 2-N Nk) (k , (Nk , refl)))
  where postulate prf : collatz ([2] ^ k) ≡ [1] → collatz n ≡ [1]
        {-# ATP prove prf helper #-}
