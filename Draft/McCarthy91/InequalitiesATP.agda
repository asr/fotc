------------------------------------------------------------------------------
-- Inequalities used by the McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.InequalitiesATP where

open import LTC.Base

open import Draft.McCarthy91.ArithmeticATP

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.Numbers

------------------------------------------------------------------------------

LMC : D → D → Set
LMC m n = LT (hundred-one ∸ m) (hundred-one ∸ n)

LMC-prop : ∀ {n} → N n → LE n one-hundred → LMC (n + eleven) n
LMC-prop zN 0≤100 = prf
  where
    postulate
      prf : (hundred-one ∸ (zero + eleven)) < (hundred-one ∸ zero) ≡ true
    {-# ATP prove prf #-}
LMC-prop (sN {n} Nn) Sn≤100 = prf (LMC-prop Nn n≤100)
  where
    n≤100 : LE n one-hundred
    n≤100 = ≤-trans Nn (sN Nn) N100 (x<y→x≤y Nn (sN Nn) (x<Sx Nn)) Sn≤100

    postulate
      prf : (hundred-one ∸ (n + eleven)) < (hundred-one ∸ n) ≡ true →  -- IH.
            (hundred-one ∸ (succ n + eleven)) < (hundred-one ∸ succ n) ≡ true
    {-# ATP prove prf #-} -- Fail with all the ATPs.
