------------------------------------------------------------------------------
-- Arithmetic properties (added for the Collatz function example)
------------------------------------------------------------------------------

module FOTC.Program.Collatz.Data.Nat.PropertiesATP where

open import FOTC.Base

open import FOTC.Base.PropertiesATP

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm zN          = subst N (sym (^-0 m)) (sN zN)
^-N {m} Nm (sN {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

postulate
  2*SSx≥2 : ∀ {n} → N n → GE (two * succ (succ n)) two
{-# ATP prove 2*SSx≥2 #-}

2x/2≡x : ∀ {n} → N n → two * n / two ≡ n
2x/2≡x zN = prf
  where
    postulate prf : two * zero / two ≡ zero
    {-# ATP prove prf *-rightZero #-}

2x/2≡x (sN zN) = prf
  where
    postulate prf : two * succ zero / two ≡ succ zero
    {-# ATP prove prf *-rightIdentity x≥x x∸x≡0 #-}

2x/2≡x (sN (sN {n} Nn)) = prf (2x/2≡x (sN Nn))
  where
    postulate prf : two * succ n / two ≡ succ n →  -- IH.
                    two * succ (succ n) / two ≡ succ (succ n)
    {-# ATP prove prf 2*SSx≥2 *-leftZero +-rightIdentity +-comm +-N #-}

postulate
  2^[x+1]/2≡x : ∀ {n} → N n → (two ^ (succ n)) / two ≡ two ^ n
{-# ATP prove 2^[x+1]/2≡x 2x/2≡x ^-N #-}

2^[x+1]-Even : ∀ n → Even (two ^ (succ n))
2^[x+1]-Even n = two ^ n , ^-S two n

Sx≡2^0→x≡0 : ∀ {n} → N n → succ n ≡ two ^ zero → n ≡ zero
Sx≡2^0→x≡0 zN         _       = refl
Sx≡2^0→x≡0(sN {n} Nn) SSn≡2^0 = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf #-}
