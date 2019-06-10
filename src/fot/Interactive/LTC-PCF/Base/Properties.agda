------------------------------------------------------------------------------
-- Interactive.LTC-PCF.terms properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Base.Properties where

open import Interactive.LTC-PCF.Base

------------------------------------------------------------------------------
-- Congruence properties

·-leftCong : ∀ {m n o} → m ≡ n → m · o ≡ n · o
·-leftCong refl = refl

·-rightCong : ∀ {m n o} → n ≡ o → m · n ≡ m · o
·-rightCong refl = refl

succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
succCong refl = refl

predCong : ∀ {m n} → m ≡ n → pred₁ m ≡ pred₁ n
predCong refl = refl

------------------------------------------------------------------------------

S≢0 : ∀ {n} → succ₁ n ≢ zero
S≢0 S≡0 = 0≢S (sym S≡0)

-- We added Common.Relation.Binary.PropositionalEquality.cong, so this
-- theorem is not necessary.
-- x≡y→Sx≡Sy : ∀ {m n} → m ≡ n → succ₁ m ≡
-- succ₁ n x≡y→Sx≡Sy refl = refl
