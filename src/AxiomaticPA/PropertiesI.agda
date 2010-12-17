------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module AxiomaticPA.PropertiesI where

open import AxiomaticPA.Base

open import AxiomaticPA.Equality.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import AxiomaticPA.Equality.Properties using ( sym )

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≣ n
+-rightIdentity = S₉ P P0 iStep
  where
    P : ℕ → Set
    P i = i + zero ≣ i

    P0 : P zero
    P0 = S₅ zero

    iStep : ∀ i → P i → P (succ i)
    iStep i Pi =
      begin
        succ i + zero   ≡⟨ S₆ i zero ⟩
        succ (i + zero) ≡⟨ S₂ Pi ⟩
        succ i
      ∎

x+1+y≣1+x+y : ∀ m n → m + succ n ≣ succ (m + n)
x+1+y≣1+x+y m n = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + succ n ≣ succ (i + n)

    P0 : P zero
    P0 =
      begin
        zero + succ n   ≡⟨ S₅ (succ n) ⟩
        succ n          ≡⟨ S₂ (sym (S₅ n)) ⟩
        succ (zero + n)
      ∎

    iStep : ∀ i → P i → P (succ i)
    iStep i Pi =
        begin
          succ i + succ n     ≡⟨ S₆ i (succ n) ⟩
          succ (i + succ n)   ≡⟨ S₂ Pi ⟩
          succ (succ (i + n)) ≡⟨ S₂ (sym (S₆ i n)) ⟩
          succ (succ i + n)
        ∎

+-comm : ∀ m n → m + n ≣ n + m
+-comm m n = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + n ≣ n + i

    P0 : P zero
    P0 =
      begin
        zero + n   ≡⟨ S₅ n ⟩
        n          ≡⟨ sym (+-rightIdentity n) ⟩
        n + zero
      ∎

    iStep : ∀ i → P i → P (succ i)
    iStep i Pi =
       begin
         succ i + n   ≡⟨ S₆ i n ⟩
         succ (i + n) ≡⟨ S₂ Pi ⟩
         succ (n + i) ≡⟨ sym (x+1+y≣1+x+y n i) ⟩
         n + succ i
       ∎
