------------------------------------------------------------------------------
-- FOTC version of a nested recursive function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001.

module FOT.FOTC.Program.Nest.Nest where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat.Type
-- import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
-- open FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI.WF-LT
-- open import FOTC.Data.Nat.Inequalities
-- open import FOTC.Data.Nat.Inequalities.PropertiesI

------------------------------------------------------------------------------

-- The nest function.
postulate
  nest   : D → D
  nest-0 : nest zero            ≡ zero
  nest-S : ∀ n → nest (succ₁ n) ≡ nest (nest n)

nest-x≡0 : ∀ {n} → N n → nest n ≡ zero
nest-x≡0 nzero = nest-0
nest-x≡0 (nsucc {n} Nn) =
  nest (succ₁ n) ≡⟨ nest-S n ⟩
  nest (nest n)  ≡⟨ cong nest (nest-x≡0 Nn) ⟩
  nest zero      ≡⟨ nest-0 ⟩
  zero           ∎

nest-N : ∀ {n} → N n → N (nest n)
nest-N Nn = subst N (sym (nest-x≡0 Nn)) nzero
