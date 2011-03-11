------------------------------------------------------------------------------
-- Axiomatic PA properties
------------------------------------------------------------------------------

module PA.Axiomatic.PropertiesI where

open import PA.Axiomatic.Base

open import PA.Axiomatic.Relation.Binary.EqReasoning
open import PA.Axiomatic.Relation.Binary.PropositionalEqualityI using ( sym )

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≣ n
+-rightIdentity = S₉ P P0 is
  where
    P : ℕ → Set
    P i = i + zero ≣ i

    P0 : P zero
    P0 = S₅ zero

    is : ∀ i → P i → P (succ i)
    is i Pi =
      begin
        succ i + zero   ≣⟨ S₆ i zero ⟩
        succ (i + zero) ≣⟨ S₂ Pi ⟩
        succ i
      ∎

x+Sy≣S[x+y] : ∀ m n → m + succ n ≣ succ (m + n)
x+Sy≣S[x+y] m n = S₉ P P0 is m
  where
    P : ℕ → Set
    P i = i + succ n ≣ succ (i + n)

    P0 : P zero
    P0 =
      begin
        zero + succ n   ≣⟨ S₅ (succ n) ⟩
        succ n          ≣⟨ S₂ (sym (S₅ n)) ⟩
        succ (zero + n)
      ∎

    is : ∀ i → P i → P (succ i)
    is i Pi =
        begin
          succ i + succ n     ≣⟨ S₆ i (succ n) ⟩
          succ (i + succ n)   ≣⟨ S₂ Pi ⟩
          succ (succ (i + n)) ≣⟨ S₂ (sym (S₆ i n)) ⟩
          succ (succ i + n)
        ∎

+-comm : ∀ m n → m + n ≣ n + m
+-comm m n = S₉ P P0 is m
  where
    P : ℕ → Set
    P i = i + n ≣ n + i

    P0 : P zero
    P0 =
      begin
        zero + n   ≣⟨ S₅ n ⟩
        n          ≣⟨ sym (+-rightIdentity n) ⟩
        n + zero
      ∎

    is : ∀ i → P i → P (succ i)
    is i Pi =
       begin
         succ i + n   ≣⟨ S₆ i n ⟩
         succ (i + n) ≣⟨ S₂ Pi ⟩
         succ (n + i) ≣⟨ sym (x+Sy≣S[x+y] n i) ⟩
         n + succ i
       ∎

x≣y→x+z≣y+z : ∀ {m n} o → m ≣ n → m + o ≣ n + o
x≣y→x+z≣y+z {m} {n} o m≣n = S₉ P P0 is o
  where
    P : ℕ → Set
    P i = m + i ≣ n + i

    P0 : P zero
    P0 =
      begin
        m + zero ≣⟨ +-rightIdentity m ⟩
        m        ≣⟨ m≣n ⟩
        n        ≣⟨ sym (+-rightIdentity n) ⟩
        n + zero
      ∎

    is : ∀ i → P i → P (succ i)
    is i Pi =
      begin
        m + succ i   ≣⟨ x+Sy≣S[x+y] m i ⟩
        succ (m + i) ≣⟨ S₂ Pi ⟩
        succ (n + i) ≣⟨ sym (x+Sy≣S[x+y] n i) ⟩
        n + succ i
      ∎

+-asocc : ∀ m n o → m + n + o ≣ m + (n + o)
+-asocc m n o = S₉ P P0 is m
  where
    P : ℕ → Set
    P i = i + n + o ≣ i + (n + o)

    P0 : P zero
    P0 =
      begin
        zero + n + o  ≣⟨ x≣y→x+z≣y+z o (S₅ n) ⟩
        n + o         ≣⟨ sym (S₅ (n + o)) ⟩
        zero + (n + o)
      ∎

    is : ∀ i → P i → P (succ i)
    is i Pi =
      begin
        succ i + n + o     ≣⟨ x≣y→x+z≣y+z o (S₆ i n) ⟩
        succ (i + n) + o   ≣⟨ S₆ (i + n) o ⟩
        succ (i + n + o)   ≣⟨ S₂ Pi ⟩
        succ (i + (n + o)) ≣⟨ sym (S₆ i (n + o)) ⟩
        succ i + (n + o)
      ∎
