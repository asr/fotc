------------------------------------------------------------------------------
-- Inductive PA properties using the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Inductive.PropertiesByInductionI where

open import PA.Inductive.Base

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≡ n + i

  A0 : A zero
  A0 = sym (+-rightIdentity n)

  is : ∀ i → A i → A (succ i)
  is i ih = succ (i + n) ≡⟨ succCong ih ⟩
            succ (n + i) ≡⟨ sym (x+Sy≡S[x+y] n i) ⟩
            n + succ i   ∎
