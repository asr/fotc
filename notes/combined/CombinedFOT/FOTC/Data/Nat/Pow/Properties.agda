------------------------------------------------------------------------------
-- Some proofs related to the power function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombinedFOT.FOTC.Data.Nat.Pow.Properties where

open import CombinedFOT.FOTC.Data.Nat.Pow

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.UnaryNumbers
open import Combined.FOTC.Data.Nat.UnaryNumbers.Totality

------------------------------------------------------------------------------

postulate 0^0≡1 : 0' ^ 0' ≡ 1'
{-# ATP prove 0^0≡1 #-}

0^Sx≡0 : ∀ {n} → N n → 0' ^ succ₁ n ≡ 0'
0^Sx≡0 {.zero} nzero  = prf
  where postulate prf : 0' ^ succ₁ zero ≡ 0'
        {-# ATP prove prf #-}

0^Sx≡0 (nsucc {n} Nn) = prf
  where postulate prf : 0' ^ succ₁ (succ₁ n) ≡ 0'
        {-# ATP prove prf #-}

thm₁ : ∀ {n} → N n → 5' ≤ n → n ^ 5' ≤ 5' ^ n
thm₁ nzero h = prf
  where postulate prf : zero ^ 5' ≤ 5' ^ zero
        {-# ATP prove prf #-}
thm₁ (nsucc {n} Nn) h = prf (thm₁ Nn) h
  where
  postulate prf : (5' ≤ n → n ^ 5' ≤ 5' ^ n) →
                  5' ≤ succ₁ n →
                  succ₁ n ^ 5' ≤ 5' ^ succ₁ n
  -- 2018-06-28: The ATPs could not prove the theorem (300 sec).
  -- {-# ATP prove prf 5-N #-}

thm₂ : ∀ {n} → N n →
       ((2' ^ n) ∸ 1') + 1' + ((2' ^ n) ∸ 1') ≡ 2' ^ (n + 1') ∸ 1'
thm₂ nzero = prf
  where
  postulate prf : ((2' ^ zero) ∸ 1') + 1' + ((2' ^ zero) ∸ 1') ≡
                  2' ^ (zero + 1') ∸ 1'
  {-# ATP prove prf #-}
thm₂ (nsucc {n} Nn) = prf (thm₂ Nn)
  where
  postulate prf : ((2' ^ n) ∸ 1') + 1' + ((2' ^ n) ∸ 1') ≡
                  2' ^ (n + 1') ∸ 1' →
                  ((2' ^ succ₁ n) ∸ 1') + 1' + ((2' ^ succ₁ n) ∸ 1') ≡
                  2' ^ (succ₁ n + 1') ∸ 1'
  -- 2018-06-28: The ATPs could not prove the theorem (300 sec).
  -- {-# ATP prove prf #-}
