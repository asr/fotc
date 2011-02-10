----------------------------------------------------------------------------
-- Well-founded induction on the relation MCR
----------------------------------------------------------------------------

module Draft.McCarthy91.WellFoundedInduction where

open import LTC.Base

open import Draft.McCarthy91.McCarthy91

open import LTC.Data.Nat

----------------------------------------------------------------------------

-- TODO: To remove the postulate.
postulate
  wfInd-MCR :
   (P : D → Set) →
   (∀ {m} → N m → (∀ {n} → N n → MCR n m → P n) → P m) →
   ∀ {n} → N n → P n
