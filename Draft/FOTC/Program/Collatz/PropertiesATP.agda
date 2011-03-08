------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

module Draft.FOTC.Program.Collatz.PropertiesATP where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

open import Draft.FOTC.Program.Collatz.Collatz
open import Draft.FOTC.Program.Collatz.Data.Nat
open import Draft.FOTC.Program.Collatz.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

collatz-2^x : ∀ {n} → N n → ∃D (λ k → N k ∧ n ≡ two ^ k) → collatz n ≡ one
collatz-2^x zN _ = collatz-0

collatz-2^x (sN {n} Nn) (.zero , zN , Sn≡2^0) = prf
  where
    postulate prf : collatz (succ n) ≡ one
    {-# ATP prove prf Sx≡2^0→x≡0 #-}

collatz-2^x (sN {n} Nn) (.(succ k) , sN {k} Nk , Sn≡2^k+1) =
  prf (collatz-2^x (^-N (sN (sN zN)) Nk) (k , Nk , refl))
  where
    postulate prf : collatz (two ^ k) ≡ one →  -- IH.
                    collatz (succ n) ≡ one
    {-# ATP prove prf 2^x-Even 2^[x+1]/2≡x #-}
