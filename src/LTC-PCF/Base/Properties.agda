------------------------------------------------------------------------------
-- LTC-PCF terms properties
------------------------------------------------------------------------------

module LTC-PCF.Base.Properties where

open import LTC-PCF.Base

------------------------------------------------------------------------------

¬S≡0 : ∀ {n} → ¬ (succ₁ n ≡ zero)
¬S≡0 S≡0 = 0≠S (sym S≡0)

-- We added Common.Relation.Binary.PropositionalEquality.cong, so this
-- theorem is not necessary.
-- x≡y→Sx≡Sy : ∀ {m n} → m ≡ n → succ₁ m ≡
-- succ₁ n x≡y→Sx≡Sy refl = refl
