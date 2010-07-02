------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

module LTC.Data.NatPCF.InequalitiesPCF where

open import LTC.Minimal

------------------------------------------------------------------------------

-- Version using lambda-abstraction.
-- lth : D → D
-- lth lt = lam (λ m → lam (λ n →
--               if (isZero n) then false
--                  else (if (isZero m) then true
--                           else (lt ∙ (pred m) ∙ (pred n)))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

lt-aux₁ : D → D → D → D
lt-aux₁ d lt e = if (isZero e) then false
                    else (if (isZero d) then true
                          else (lt ∙ (pred d) ∙ (pred e)))
{-# ATP definition lt-aux₁ #-}

lt-aux₂ : D → D → D
lt-aux₂ lt d = lam (lt-aux₁ d lt)
{-# ATP definition lt-aux₂ #-}

lth : D → D
lth lt = lam (lt-aux₂ lt)
{-# ATP definition lth #-}

lt : D → D → D
lt d e = fix lth ∙ d ∙ e
{-# ATP definition lt #-}

gt : D → D → D
gt d e = lt e d
{-# ATP definition gt #-}

------------------------------------------------------------------------
-- The data types

-- infix 4 _≤_ _<_ _≥_ _>_

GT : D → D → Set
GT d e = lt e d ≡ true
{-# ATP definition GT #-}

LT : D → D  → Set
LT d e = lt d e ≡ true
{-# ATP definition LT #-}

LE : D → D → Set
LE d e = lt e d ≡ false
{-# ATP definition LE #-}

GE : D → D → Set
GE d e = lt d e ≡ false
{-# ATP definition GE #-}

------------------------------------------------------------------------------
-- The lexicographical order
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
{-# ATP definition LT₂ #-}

