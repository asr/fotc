------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.ConversionRulesATP
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

collatz-2^x : ∀ {n} → N n → (∃[ k ] N k ∧ n ≡ two ^ k) → collatz n ≡ one
collatz-2^x nzero _ = collatz-0

collatz-2^x (nsucc {n} Nn) (.zero , nzero , Sn≡2^0) = prf
  where
  postulate prf : collatz (succ₁ n) ≡ one
  {-# ATP prove prf Sx≡2^0→x≡0 #-}

collatz-2^x (nsucc {n} Nn) (.(succ₁ k) , nsucc {k} Nk , Sn≡2^k+1) = prf
  where
  -- See the interactive proof.
  postulate prf : collatz (succ₁ n) ≡ one
