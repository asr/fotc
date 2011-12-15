------------------------------------------------------------------------------
-- Inductive PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.PropertiesI where

open import PA.Inductive.Base

open import PA.Inductive.Properties
open import PA.Inductive.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero     n = sym (+-rightIdentity n)
+-comm (succ m) n =
  begin
    succ m + n   ≡⟨ refl ⟩
    succ (m + n) ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + succ m
  ∎
