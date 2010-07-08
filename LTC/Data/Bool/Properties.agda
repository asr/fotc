------------------------------------------------------------------------------
-- The booleans properties
------------------------------------------------------------------------------

module LTC.Data.Bool.Properties where

open import LTC.Minimal
open import LTC.Data.Bool
open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.Properties using ( ≤-SS ; S≰0 )

------------------------------------------------------------------------------
-- Basic properties.

-- This function is a general hint.
&&-Bool : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → Bool (b₁ && b₂)
&&-Bool tB tB = prf
  where
    postulate prf : Bool (true && true)
    {-# ATP prove prf #-}
&&-Bool tB fB = prf
  where
    postulate prf : Bool (true && false)
    {-# ATP prove prf #-}
&&-Bool fB tB = prf
  where
    postulate prf : Bool (false && true)
    {-# ATP prove prf #-}
&&-Bool fB fB = prf
  where
    postulate prf : Bool (false && false)
    {-# ATP prove prf #-}
{-# ATP hint &&-Bool #-}

x&&y≡true→x≡true : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true →
                   b₁ ≡ true
x&&y≡true→x≡true tB _ _    = refl
x&&y≡true→x≡true fB tB prf = ⊥-elim (true≠false (trans (sym prf) &&-ft))
x&&y≡true→x≡true fB fB prf = ⊥-elim (true≠false (trans (sym prf) &&-ff))

x&&y≡true→y≡true : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true →
                   b₂ ≡ true
x&&y≡true→y≡true _  tB _   = refl
x&&y≡true→y≡true tB fB prf = ⊥-elim (true≠false (trans (sym prf) &&-tf))
x&&y≡true→y≡true fB fB prf = ⊥-elim (true≠false (trans (sym prf) &&-ff))

------------------------------------------------------------------------------
-- Properties with inequalities

-- This function is a general hint.
≤-Bool : {m n : D} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn = prf
  where
    postulate prf : Bool (zero ≤ n)
    {-# ATP prove prf #-}
≤-Bool (sN {m} Nm) zN = prf
  where
    postulate prf : Bool (succ m ≤ zero)
    {-# ATP prove prf S≰0 #-}
≤-Bool (sN {m} Nm) (sN {n} Nn) = prf (≤-Bool Nm Nn)
  where
    postulate prf : Bool (m ≤ n) → Bool (succ m ≤ succ n)
    {-# ATP prove prf #-}
{-# ATP hint ≤-Bool #-}



