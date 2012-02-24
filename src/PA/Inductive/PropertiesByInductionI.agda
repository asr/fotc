------------------------------------------------------------------------------
-- Inductive PA properties using the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.PropertiesByInductionI where

open import PA.Inductive.Base

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = PA-ind P P0 is m
  where
  P : M → Set
  P i = i + n ≡ n + i

  P0 : P zero
  P0 = sym (+-rightIdentity n)

  is : ∀ i → P i → P (succ i)
  is i ih = succ i + n   ≡⟨ refl ⟩
            succ (i + n) ≡⟨ cong succ ih ⟩
            succ (n + i) ≡⟨ sym (x+Sy≡S[x+y] n i) ⟩
            n + succ i ∎
