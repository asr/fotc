------------------------------------------------------------------------------
-- Commutativity of addition
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.PA.Axiomatic.Standard.AddComm where

open import Common.FOL.Relation.Binary.EqReasoning

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------
-- Auxiliary functions

succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succCong = cong succ

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = PA₃

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = PA-ind A A0 is
  where
  A : M → Set
  A i = i + zero ≡ i

  A0 : A zero
  A0 = +-leftIdentity zero

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + zero   ≡⟨ PA₄ i zero ⟩
            succ (i + zero) ≡⟨ succCong ih ⟩
            succ i          ∎

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = PA-ind A A0 is m
  where
  A : M → Set
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

------------------------------------------------------------------------------
-- Interactive proof

+-comm₁ : ∀ m n → m + n ≡ n + m
+-comm₁ m n = PA-ind A A0 is m
  where
  A : M → Set
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

------------------------------------------------------------------------------
-- Combined proof

+-comm₂ : ∀ m n → m + n ≡ n + m
+-comm₂ m n = PA-ind A A0 is m
  where
  A : M → Set
  A i = i + n ≡ n + i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is x+Sy≡S[x+y] #-}

------------------------------------------------------------------------------
-- Interactive proof instantiating the induction principle

+-comm-ind : ∀ n →
             (zero + n ≡ n + zero) →
             (∀ m → m + n ≡ n + m → succ m + n ≡ n + succ m) →
             ∀ m → m + n ≡ n + m
+-comm-ind n = PA-ind (λ i → i + n ≡ n + i)

+-comm₃ : ∀ m n → m + n ≡ n + m
+-comm₃ m n = +-comm-ind n base is m
  where
  base : zero + n ≡ n + zero
  base = zero + n ≡⟨ +-leftIdentity n ⟩
         n        ≡⟨ sym (+-rightIdentity n) ⟩
         n + zero ∎

  is : ∀ i → i + n ≡ n + i → succ i + n ≡ n + succ i
  is i ih = succ i + n   ≡⟨ PA₄ i n ⟩
            succ (i + n) ≡⟨ succCong ih ⟩
            succ (n + i) ≡⟨ sym (x+Sy≡S[x+y] n i) ⟩
            n + succ i   ∎

------------------------------------------------------------------------------
-- Combined proof instantiating the induction principle

-- TODO. 25 October 2012. Why is it not necessary the hypothesis
-- +-rightIdentity ?
postulate +-comm₄ : ∀ m n → m + n ≡ n + m
{-# ATP prove +-comm₄ +-comm-ind x+Sy≡S[x+y] #-}
