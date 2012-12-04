------------------------------------------------------------------------------
-- FOTC terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open FOTC.Base.BList

------------------------------------------------------------------------------
-- Congruence properties

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

∷-injective : ∀ {x y xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
∷-injective {x} {y} {xs} {ys} h = x≡y , xs≡ys
  where
  x≡y : x ≡ y
  x≡y = x              ≡⟨ sym (head-∷ x xs) ⟩
        head₁ (x ∷ xs) ≡⟨ cong head₁ h ⟩
        head₁ (y ∷ ys) ≡⟨ head-∷ y ys ⟩
        y              ∎

  xs≡ys : xs ≡ ys
  xs≡ys = xs             ≡⟨ sym (tail-∷ x xs) ⟩
          tail₁ (x ∷ xs) ≡⟨ cong tail₁ h ⟩
          tail₁ (y ∷ ys) ≡⟨ tail-∷ y ys ⟩
          ys             ∎
