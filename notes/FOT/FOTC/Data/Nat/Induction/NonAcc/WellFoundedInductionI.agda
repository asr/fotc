----------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
----------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Induction.NonAcc.WellFoundedInductionI where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers.

wfInd-LT : (P : D → Set) →
           (∀ {n} → N n → (∀ {m} → N m → LT m n → P m) → P n) →
           ∀ {n} → N n → P n
wfInd-LT P accH nzero      = accH nzero (λ Nm m<0 → ⊥-elim (x<0→⊥ Nm m<0))
wfInd-LT P accH (nsucc Nn) = accH (nsucc Nn)
                               (λ Nm m<Sn → helper Nm Nn (wfInd-LT P accH Nn)
                                                   (x<Sy→x≤y Nm Nn m<Sn))
  where
    helper : ∀ {n m} → N n → N m → P m → LE n m → P n
    helper {n} {m} Nn Nm Pm n≤m = case (λ n<m → {!!} )
                                  (λ n≡m → helper₁ n≡m Pm)
                                  (x≤y→x<y∨x≡y Nn Nm n≤m)
      where
        helper₁ : ∀ {a b} → a ≡ b → P b → P a
        helper₁ refl Pb = Pb
