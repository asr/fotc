------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Nat.Inequalities where

open import Interactive.FOTC.Base

infix 4 _<_ _≮_ _>_ _≯_ _≤_ _≰_ _≥_ _≱_

------------------------------------------------------------------------------
-- The function terms.

postulate
  lt    : D → D → D
  lt-00 : lt zero zero                   ≡ false
  lt-0S : ∀ n → lt zero (succ₁ n)        ≡ true
  lt-S0 : ∀ n → lt (succ₁ n) zero        ≡ false
  lt-SS : ∀ m n → lt (succ₁ m) (succ₁ n) ≡ lt m n

le : D → D → D
le m n = lt m (succ₁ n)

gt : D → D → D
gt m n = lt n m

ge : D → D → D
ge m n = le n m

------------------------------------------------------------------------
-- The relations.

_<_ : D → D → Set
m < n = lt m n ≡ true

_≮_ : D → D → Set
m ≮ n = lt m n ≡ false

_>_ : D → D → Set
m > n = gt m n ≡ true

_≯_ : D → D → Set
m ≯ n = gt m n ≡ false

_≤_  : D → D → Set
m ≤ n = le m n ≡ true

_≰_  : D → D → Set
m ≰ n = le m n ≡ false

_≥_ : D → D → Set
m ≥ n = ge m n ≡ true

_≱_ : D → D → Set
m ≱ n = ge m n ≡ false

------------------------------------------------------------------------------
-- The lexicographical order.
Lexi : D → D → D → D → Set
Lexi m n m' n' = m < m' ∨ m ≡ m' ∧ n < n'
