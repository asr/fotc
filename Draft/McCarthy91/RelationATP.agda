------------------------------------------------------------------------------
-- Properties for some relations
------------------------------------------------------------------------------

module Draft.McCarthy91.RelationATP where

open import LTC.Base

open import Draft.McCarthy91.McCarthy91
open import Draft.McCarthy91.ArithmeticATP

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.Numbers

------------------------------------------------------------------------------

MCR-prop : ∀ {n} → N n → LE n one-hundred → MCR (n + eleven) n
MCR-prop zN 0≤100 = prf
  where
    postulate
      prf : (hundred-one ∸ (zero + eleven)) < (hundred-one ∸ zero) ≡ true
    {-# ATP prove prf #-}
MCR-prop (sN {n} Nn) Sn≤100 = prf (MCR-prop Nn n≤100)
  where
    n≤100 : LE n one-hundred
    n≤100 = ≤-trans Nn (sN Nn) N100 (x<y→x≤y Nn (sN Nn) (x<Sx Nn)) Sn≤100

    postulate
      prf : (hundred-one ∸ (n + eleven)) < (hundred-one ∸ n) ≡ true →  -- IH.
            (hundred-one ∸ (succ n + eleven)) < (hundred-one ∸ succ n) ≡ true
    {-# ATP prove prf #-} -- Fail with all the ATPs.
