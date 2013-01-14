------------------------------------------------------------------------------
-- Filter
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.List.Filter where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Base.List
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI

------------------------------------------------------------------------------

postulate
  filter    : D → D → D
  filter-[] : ∀ p → filter p [] ≡ []
  filter-∷  : ∀ p x xs → filter p (x ∷ xs) ≡
              if p · x then x ∷ filter p xs else filter p xs

postulate filter-List : ∀ p {xs} → List xs → List (filter p xs)

from-Bool : ∀ {b} → Bool b → b ≡ true ∨ b ≡ false
from-Bool btrue  = inj₁ refl
from-Bool bfalse = inj₂ refl

-- lenght-filter : ∀ p {xs} → (∀ x → Bool (p · x)) → List xs →
--                 length (filter p xs) ≤ length xs
-- lenght-filter p hp lnil =
--   le (length (filter p [])) (length [])
--     ≡⟨ ltLeftCong (lengthCong (filter-[] p)) ⟩
--   le (length []) (length [])
--     ≡⟨ ltCong length-[] (succCong length-[]) ⟩
--   le zero zero
--     ≡⟨ x≤x nzero ⟩
--   true ∎

-- lenght-filter p hp (lcons x {xs} Lxs) = case prf₁ prf₂ (from-Bool (hp x))
--   where
--   prf₁ : p · x ≡ true →
--          le (length (filter p (x ∷ xs))) (length (x ∷ xs)) ≡ true
--   prf₁ h = {!!}

--   prf₂ : p · x ≡ false →
--          le (length (filter p (x ∷ xs))) (length (x ∷ xs)) ≡ true
--   prf₂ h =
--     le (length (filter p (x ∷ xs))) (length (x ∷ xs))
--       ≡⟨ ltLeftCong (lengthCong {!!}) ⟩
--     le (length (filter p xs)) (length (x ∷ xs))
--       ≡⟨ ≤-trans (lengthList-N (filter-List p Lxs))
--                  (lengthList-N Lxs)
--                  (lengthList-N (lcons x Lxs))
--                  (lenght-filter p hp Lxs)
--                  (x<y→x≤y (lengthList-N Lxs) (lengthList-N (lcons x Lxs))
--                           (lg-x<lg-x∷xs x Lxs)) ⟩
--     true ∎
