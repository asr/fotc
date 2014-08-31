------------------------------------------------------------------------------
-- Properties of the iter₀ function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Iter0.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.PropertiesI
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
        (lncons (nsucc Nn) (iter₀-ListN f (h (nsucc Nn)) h))
  where
  prf : iter₀ f (succ₁ n) ≡ succ₁ n ∷ iter₀ f (f · (succ₁ n))
  prf = iter₀ f (succ₁ n)
          ≡⟨ iter₀-eq f (succ₁ n) ⟩
        (if (iszero₁ (succ₁ n)) then [] else (succ₁ n ∷ iter₀ f (f · (succ₁ n))))
          ≡⟨ ifCong₁ (iszero-S n) ⟩
        (if false then [] else (succ₁ n ∷ iter₀ f (f · (succ₁ n))))
          ≡⟨ if-false (succ₁ n ∷ iter₀ f (f · (succ₁ n))) ⟩
        succ₁ n ∷ iter₀ f (f · (succ₁ n)) ∎
