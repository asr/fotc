------------------------------------------------------------------------------
-- FOTC list terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

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

∷-cong : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
∷-cong refl refl = refl

headCong : ∀ {xs ys} → xs ≡ ys → head₁ xs ≡ head₁ ys
headCong refl = refl

tailCong : ∀ {xs ys} → xs ≡ ys → tail₁ xs ≡ tail₁ ys
tailCong refl = refl

------------------------------------------------------------------------------
-- Injective properties

∷-injective : ∀ {x y xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
∷-injective {x} {y} {xs} {ys} h = x≡y , xs≡ys
  where
  x≡y : x ≡ y
  x≡y = x              ≡⟨ sym (head-∷ x xs) ⟩
        head₁ (x ∷ xs) ≡⟨ headCong h ⟩
        head₁ (y ∷ ys) ≡⟨ head-∷ y ys ⟩
        y              ∎

  xs≡ys : xs ≡ ys
  xs≡ys = xs             ≡⟨ sym (tail-∷ x xs) ⟩
          tail₁ (x ∷ xs) ≡⟨ tailCong h ⟩
          tail₁ (y ∷ ys) ≡⟨ tail-∷ y ys ⟩
          ys             ∎
