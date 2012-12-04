------------------------------------------------------------------------------
-- Properties of the function iter₀
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Iter0.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
open FOTC.Base.BList
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.List.Type
open import FOTC.Program.Iter0.Iter0
open import FOTC.Program.Iter0.PropertiesI

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
iter₀-ListN : ∀ f {n} → N n → (∀ {n} → N n → N (f · n)) → ListN (iter₀ f n)
iter₀-ListN f nzero h = subst ListN (sym (iter₀-0 f)) lnnil
iter₀-ListN f (nsucc {n} Nn) h =
  subst ListN
        (sym prf)
        (lncons Nn (iter₀-ListN f (h Nn) h))
  where
  prf : iter₀ f (succ₁ n) ≡ n ∷ iter₀ f (f · n)
  prf = iter₀ f (succ₁ n)
          ≡⟨ iter₀-eq f (succ₁ n) ⟩
        if (iszero₁ (succ₁ n))
           then []
           else (pred₁ (succ₁ n) ∷ iter₀ f (f · pred₁ (succ₁ n)))
          ≡⟨ ifCong₁ (iszero-S n) ⟩
        if false
           then []
           else (pred₁ (succ₁ n) ∷ iter₀ f (f · pred₁ (succ₁ n)))
          ≡⟨ if-false (pred₁ (succ₁ n) ∷ iter₀ f (f · pred₁ (succ₁ n))) ⟩
        pred₁ (succ₁ n) ∷ iter₀ f (f · pred₁ (succ₁ n))
          ≡⟨ ∷-leftCong (pred-S n) ⟩
        n ∷ iter₀ f (f · pred₁ (succ₁ n))
          ≡⟨ subst (λ t → n ∷ iter₀ f (f · pred₁ (succ₁ n)) ≡ n ∷ iter₀ f (f · t))
                   (pred-S n)
                   refl
          ⟩
        n ∷ iter₀ f (f · n) ∎
