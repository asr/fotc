------------------------------------------------------------------------------
-- FOTC list terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.List.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- Congruence properties

∷-leftCong : ∀ {x y xs} → x ≡ y → x ∷ xs ≡ y ∷ xs
∷-leftCong refl = refl

∷-rightCong : ∀ {x xs ys} → xs ≡ ys → x ∷ xs ≡ x ∷ ys
∷-rightCong refl = refl

∷-Cong : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
∷-Cong refl refl = refl

------------------------------------------------------------------------------
-- Injective properties

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
