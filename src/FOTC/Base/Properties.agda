------------------------------------------------------------------------------
-- FOTC terms properties
------------------------------------------------------------------------------

module FOTC.Base.Properties where

open import FOTC.Base

open import Common.Function

------------------------------------------------------------------------------

≡-list : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
≡-list {y = y} {ys = ys} x≡y xs≡ys =
  subst₂ (λ x' xs' → x' ∷ xs' ≡ y ∷ ys) (sym x≡y) (sym xs≡ys) refl

≡-stream : ∀ {x y xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
≡-stream = ≡-list

¬S≡0 : ∀ {n} → ¬ (succ n ≡ zero)
¬S≡0 S≡0 = 0≠S $ sym S≡0

-- We added Common.Relation.Binary.PropositionalEquality.cong, so this
-- theorem is not necessary.
-- x≡y→Sx≡Sy : ∀ {m n} → m ≡ n → succ m ≡
-- succ n x≡y→Sx≡Sy refl = refl
