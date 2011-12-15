------------------------------------------------------------------------------
-- FOTC terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.Properties where

open import Common.Function
open import FOTC.Base

------------------------------------------------------------------------------

≡-list : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
≡-list {y = y} {ys = ys} x≡y xs≡ys =
  subst₂ (λ x' xs' → x' ∷ xs' ≡ y ∷ ys) (sym x≡y) (sym xs≡ys) refl

≡-stream : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
≡-stream = ≡-list

¬S≡0 : ∀ {n} → ¬ (succ₁ n ≡ zero)
¬S≡0 S≡0 = 0≠S $ sym S≡0

-- We added Common.Relation.Binary.PropositionalEquality.cong, so this
-- theorem is not necessary.
-- x≡y→Sx≡Sy : ∀ {m n} → m ≡ n → succ₁ m ≡
-- succ₁ n x≡y→Sx≡Sy refl = refl
