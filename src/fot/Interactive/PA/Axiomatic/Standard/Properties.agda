------------------------------------------------------------------------------
-- Axiomatic PA properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.PA.Axiomatic.Standard.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------
-- Congruence properties

succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succCong refl = refl

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong refl = refl

+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong refl = refl

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = PA₃

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = ℕ-ind A A0 is
  where
  A : ℕ → Set
  A i = i + zero ≡ i

  A0 : A zero
  A0 = +-leftIdentity zero

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + zero   ≡⟨ PA₄ i zero ⟩
            succ (i + zero) ≡⟨ succCong ih ⟩
            succ i          ∎

+-asocc : ∀ m n o → m + n + o ≡ m + (n + o)
+-asocc m n o = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≡ i + (n + o)

  A0 : A zero
  A0 = zero + n + o   ≡⟨ +-leftCong (+-leftIdentity n) ⟩
       n + o          ≡⟨ sym (+-leftIdentity (n + o)) ⟩
       zero + (n + o) ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n + o     ≡⟨ +-leftCong (PA₄ i n) ⟩
            succ (i + n) + o   ≡⟨ PA₄ (i + n) o ⟩
            succ (i + n + o)   ≡⟨ succCong ih ⟩
            succ (i + (n + o)) ≡⟨ sym (PA₄ i (n + o)) ⟩
            succ i + (n + o)   ∎

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + succ n ≡ succ (i + n)

  A0 : A zero
  A0 = zero + succ n   ≡⟨ +-leftIdentity (succ n) ⟩
       succ n          ≡⟨ succCong (sym (+-leftIdentity n)) ⟩
       succ (zero + n) ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + succ n     ≡⟨ PA₄ i (succ n) ⟩
            succ (i + succ n)   ≡⟨ succCong ih ⟩
            succ (succ (i + n)) ≡⟨ succCong (sym (PA₄ i n)) ⟩
            succ (succ i + n)   ∎

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≡ n + i

  A0 : A zero
  A0 = zero + n ≡⟨ +-leftIdentity n ⟩
       n        ≡⟨ sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n   ≡⟨ PA₄ i n ⟩
            succ (i + n) ≡⟨ succCong ih ⟩
            succ (n + i) ≡⟨ sym (x+Sy≡S[x+y] n i) ⟩
            n + succ i   ∎
