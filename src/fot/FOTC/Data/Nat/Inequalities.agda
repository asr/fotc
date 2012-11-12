------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities where

open import FOTC.Base

-- We add 4 to the fixities of the standard library.
infix 8 _<_ _≮_ _>_ _≯_ _≤_ _≰_ _≥_ _≱_

------------------------------------------------------------------------------

postulate
  lt  : D → D → D
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
-- The data types

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
Lexi m₁ n₁ m₂ n₂ = m₁ < m₂ ∨ m₁ ≡ m₂ ∧ n₁ < n₂
{-# ATP definition Lexi #-}
