------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Collatz.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesATP using ( ∸-N )
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP using ( 2-N )
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

helper : ∀ {n} → N n → collatz (2' ^ succ₁ n) ≡ collatz (2' ^ n)
helper nzero = prf
  where postulate prf : collatz (2' ^ succ₁ zero) ≡ collatz (2' ^ zero)
        {-# ATP prove prf #-}
helper (nsucc {n} Nn) = prf
  where postulate prf : collatz (2' ^ succ₁ (succ₁ n)) ≡ collatz (2' ^ succ₁ n)
        {-# ATP prove prf +∸2 ^-N 2-N 2^x≢0 2^[x+1]≢1 div-2^[x+1]-2≡2^x
                      x-Even→SSx-Even ∸-N ∸-Even 2^[x+1]-Even 2-Even
        #-}

collatz-2^x : ∀ {n} → N n → collatz (2' ^ n) ≡ 1'
collatz-2^x nzero = prf
  where postulate prf : collatz (2' ^ 0') ≡ 1'
        {-# ATP prove prf #-}

collatz-2^x (nsucc {n} Nn) = prf (collatz-2^x Nn)
  where postulate prf : collatz (2' ^ n) ≡ 1' → collatz (2' ^ succ₁ n) ≡ 1'
        {-# ATP prove prf helper #-}
