------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

module FOTC.Program.Collatz.PropertiesATP where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

collatz-2^x : ∀ {n} → N n → ∃ (λ k → N k ∧ n ≡ two ^ k) → collatz n ≡ one
collatz-2^x zN _ = collatz-0

collatz-2^x (sN {n} Nn) (.zero , zN , Sn≡2^0) = prf
  where
    postulate prf : collatz (succ n) ≡ one
    {-# ATP prove prf Sx≡2^0→x≡0 #-}

collatz-2^x (sN {n} Nn) (.(succ k) , sN {k} Nk , Sn≡2^k+1) =
  prf (collatz-2^x (^-N 2-N Nk) (k , Nk , refl))
  where
    postulate prf : collatz (two ^ k) ≡ one →  -- IH.
                    collatz (succ n) ≡ one
    {-# ATP prove prf 2^[x+1]-Even 2^[x+1]/2≡2^x #-}
