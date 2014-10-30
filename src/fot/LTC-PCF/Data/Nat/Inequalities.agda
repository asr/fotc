------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat.Inequalities where

open import LTC-PCF.Base

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/Nat.Agda).
infix 7 _<_ _≮_ _<_ _≮_ _≤_ _≰_ _≥_ _≱_

------------------------------------------------------------------------------
-- The function terms.

lth : D → D
lth lt = lam (λ m → lam (λ n →
           if (iszero₁ n)
             then false
             else (if (iszero₁ m) then true else (lt · pred₁ m · pred₁ n))))
lt : D → D → D
lt m n = fix lth · m · n

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
