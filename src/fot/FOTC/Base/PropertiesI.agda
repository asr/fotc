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
