------------------------------------------------------------------------------
-- Axiomatic PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Standard.PropertiesI where

open import FOL.Relation.Binary.EqReasoning

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------
-- Congruence properties

succ-cong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succ-cong = cong succ

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong h = cong₂ _+_ h refl

+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong = cong₂ _+_ refl

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = A₇ P P0 is
  where
  P : M → Set
  P i = i + zero ≡ i

  P0 : P zero
  P0 = A₃ zero

  is : ∀ i → P i → P (succ i)
  is i Pi = succ i + zero   ≡⟨ A₄ i zero ⟩
            succ (i + zero) ≡⟨ succ-cong Pi ⟩
            succ i ∎


+-asocc : ∀ m n o → m + n + o ≡ m + (n + o)
+-asocc m n o = A₇ P P0 is m
  where
  P : M → Set
  P i = i + n + o ≡ i + (n + o)

  P0 : P zero
  P0 = zero + n + o  ≡⟨ +-leftCong (A₃ n) ⟩
       n + o         ≡⟨ sym (A₃ (n + o)) ⟩
       zero + (n + o) ∎

  is : ∀ i → P i → P (succ i)
  is i Pi = succ i + n + o     ≡⟨ +-leftCong (A₄ i n) ⟩
            succ (i + n) + o   ≡⟨ A₄ (i + n) o ⟩
            succ (i + n + o)   ≡⟨ succ-cong Pi ⟩
            succ (i + (n + o)) ≡⟨ sym (A₄ i (n + o)) ⟩
            succ i + (n + o) ∎

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = A₇ P P0 is m
  where
  P : M → Set
  P i = i + succ n ≡ succ (i + n)

  P0 : P zero
  P0 = zero + succ n   ≡⟨ A₃ (succ n) ⟩
       succ n          ≡⟨ succ-cong (sym (A₃ n)) ⟩
       succ (zero + n) ∎

  is : ∀ i → P i → P (succ i)
  is i Pi = succ i + succ n     ≡⟨ A₄ i (succ n) ⟩
            succ (i + succ n)   ≡⟨ succ-cong Pi ⟩
            succ (succ (i + n)) ≡⟨ succ-cong (sym (A₄ i n)) ⟩
            succ (succ i + n) ∎

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = A₇ P P0 is m
  where
  P : M → Set
  P i = i + n ≡ n + i

  P0 : P zero
  P0 = zero + n   ≡⟨ A₃ n ⟩
       n          ≡⟨ sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → P i → P (succ i)
  is i Pi = succ i + n   ≡⟨ A₄ i n ⟩
            succ (i + n) ≡⟨ succ-cong Pi ⟩
            succ (n + i) ≡⟨ sym (x+Sy≡S[x+y] n i) ⟩
            n + succ i ∎
