------------------------------------------------------------------------------
-- LTC-PCF terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Base.Properties where

open import LTC-PCF.Base

------------------------------------------------------------------------------
-- Congruence properties

·-leftCong : ∀ {m n o} → m ≡ n → m · o ≡ n · o
·-leftCong h = cong₂ _·_ h refl

·-rightCong : ∀ {m n o} → n ≡ o → m · n ≡ m · o
·-rightCong h = cong₂ _·_ refl h

------------------------------------------------------------------------------

S≢0 : ∀ {n} → succ₁ n ≢ zero
S≢0 S≡0 = 0≢S (sym S≡0)

-- We added Common.Relation.Binary.PropositionalEquality.cong, so this
-- theorem is not necessary.
-- x≡y→Sx≡Sy : ∀ {m n} → m ≡ n → succ₁ m ≡
-- succ₁ n x≡y→Sx≡Sy refl = refl
