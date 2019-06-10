------------------------------------------------------------------------------
-- FOTC version of a nested recursive function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001.

module InteractiveFOT.FOTC.Program.Nest.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Program.Nest.Nest

------------------------------------------------------------------------------

nestCong : ∀ {m n} → m ≡ n → nest m ≡ nest n
nestCong refl = refl

nest-x≡0 : ∀ {n} → N n → nest n ≡ zero
nest-x≡0 nzero = nest-0
nest-x≡0 (nsucc {n} Nn) =
  nest (succ₁ n) ≡⟨ nest-S n ⟩
  nest (nest n)  ≡⟨ nestCong (nest-x≡0 Nn) ⟩
  nest zero      ≡⟨ nest-0 ⟩
  zero           ∎

nest-N : ∀ {n} → N n → N (nest n)
nest-N Nn = subst N (sym (nest-x≡0 Nn)) nzero
