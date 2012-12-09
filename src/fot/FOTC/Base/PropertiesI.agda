------------------------------------------------------------------------------
-- FOTC terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base

------------------------------------------------------------------------------
-- Congruence properties

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong refl = refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong refl = refl

·-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a · c ≡ b · d
·-cong refl refl = refl

succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
succCong refl = refl

predCong : ∀ {m n} → m ≡ n → pred₁ m ≡ pred₁ n
predCong refl = refl

ifCong₁ : ∀ {b₁ b₂ d e} → b₁ ≡ b₂ → if b₁ then d else e ≡ if b₂ then d else e
ifCong₁ refl = refl

ifCong₂ : ∀ {b d₁ d₂ e} → d₁ ≡ d₂ → if b then d₁ else e ≡ if b then d₂ else e
ifCong₂ refl = refl

ifCong₃ : ∀ {b d e₁ e₂} → e₁ ≡ e₂ → if b then d else e₁ ≡ if b then d else e₂
ifCong₃ refl = refl

------------------------------------------------------------------------------
-- Injective properties

succInjective : ∀ {m n} → succ₁ m ≡ succ₁ n → m ≡ n
succInjective {m} {n} h =
  m                ≡⟨ sym (pred-S m) ⟩
  pred₁ (succ₁ m)  ≡⟨ cong pred₁ h ⟩
  pred₁ (succ₁ n)  ≡⟨ pred-S n ⟩
  n                ∎

------------------------------------------------------------------------------

S≢0 : ∀ {n} → succ₁ n ≢ zero
S≢0 S≡0 = 0≢S (sym S≡0)
