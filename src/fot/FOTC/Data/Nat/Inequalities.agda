------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities where

open import FOTC.Base

-- We add 3 to the fixities of the Agda standard library 0.6 (see
-- Data/Nat.agda).
infix 7 _<_ _≮_ _>_ _≯_ _≤_ _≰_ _≥_ _≱_

------------------------------------------------------------------------------
-- The function terms.

postulate
  lt    : D → D → D
  lt-00 : lt zero zero                   ≡ false
  lt-0S : ∀ n → lt zero (succ₁ n)        ≡ true
  lt-S0 : ∀ n → lt (succ₁ n) zero        ≡ false
  lt-SS : ∀ m n → lt (succ₁ m) (succ₁ n) ≡ lt m n
{-# ATP axiom lt-00 lt-0S lt-S0 lt-SS #-}

le : D → D → D
le m n = lt m (succ₁ n)
{-# ATP definition le #-}

gt : D → D → D
gt m n = lt n m
{-# ATP definition gt #-}

ge : D → D → D
ge m n = le n m
{-# ATP definition ge #-}

------------------------------------------------------------------------
-- The relations.

_<_ : D → D → Set
m < n = lt m n ≡ true
{-# ATP definition _<_ #-}

_≮_ : D → D → Set
m ≮ n = lt m n ≡ false
{-# ATP definition _≮_ #-}

_>_ : D → D → Set
m > n = gt m n ≡ true
{-# ATP definition _>_ #-}

_≯_ : D → D → Set
m ≯ n = gt m n ≡ false
{-# ATP definition _≯_ #-}

_≤_  : D → D → Set
m ≤ n = le m n ≡ true
{-# ATP definition _≤_ #-}

_≰_  : D → D → Set
m ≰ n = le m n ≡ false
{-# ATP definition _≰_ #-}

_≥_ : D → D → Set
m ≥ n = ge m n ≡ true
{-# ATP definition _≥_ #-}

_≱_ : D → D → Set
m ≱ n = ge m n ≡ false
{-# ATP definition _≱_ #-}

------------------------------------------------------------------------------
-- The lexicographical order.
Lexi : D → D → D → D → Set
Lexi m n m' n' = m < m' ∨ m ≡ m' ∧ n < n'
{-# ATP definition Lexi #-}
