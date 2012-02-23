------------------------------------------------------------------------------
-- A Peano arithmetic proof without using a where clause
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT on 23 February 2012.

-- See the original proof in
-- PA.Axiomatic.Relation.Binary.PropositionalEqualityI where

module NoWhere where

open import FOL.Relation.Binary.EqReasoning

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------

postulate
  +-rightIdentity : ∀ n → n + zero ≡ n
  x+Sy≡S[x+y]     : ∀ m n → m + succ n ≡ succ (m + n)
  succ-cong       : ∀ {m n} → m ≡ n → succ m ≡ succ n

P : M → M → Set
P n i = i + n ≡ n + i

P0 : ∀ n → P n zero
P0 n = zero + n   ≡⟨ A₃ n ⟩
       n          ≡⟨ sym (+-rightIdentity n) ⟩
       n + zero ∎

is : ∀ n i → P n i → P n (succ i)
is n i Pi = succ i + n   ≡⟨ A₄ i n ⟩
            succ (i + n) ≡⟨ succ-cong Pi ⟩
            succ (n + i) ≡⟨ sym (x+Sy≡S[x+y] n i) ⟩
            n + succ i ∎

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = A₇ (P n) (P0 n) (is n) m
