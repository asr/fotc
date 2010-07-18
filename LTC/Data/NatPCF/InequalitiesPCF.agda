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

_<_ : D → D → D
d < e = fix lth ∙ d ∙ e
{-# ATP definition _<_ #-}

le : D → D → D
le d e = d < (succ e)
{-# ATP definition le #-}

gt : D → D → D
gt d e = e < d
{-# ATP definition gt #-}

ge : D → D → D
ge d e = le e d
{-# ATP definition ge #-}

------------------------------------------------------------------------
-- The data types

GT : D → D → Set
GT d e = gt d e ≡ true
{-# ATP definition GT #-}

NGT : D → D → Set
NGT d e = gt d e ≡ false
{-# ATP definition NGT #-}

LT : D → D  → Set
LT d e = d < e ≡ true
{-# ATP definition LT #-}

NLT : D → D  → Set
NLT d e = d < e ≡ false
{-# ATP definition NLT #-}

LE : D → D → Set
LE d e = le d e ≡ true
{-# ATP definition LE #-}

NLE : D → D → Set
NLE d e = le d e ≡ false
{-# ATP definition NLE #-}

GE : D → D → Set
GE d e = ge d e ≡ true
{-# ATP definition GE #-}

NGE : D → D → Set
NGE d e = ge d e ≡ false
{-# ATP definition NGE #-}

------------------------------------------------------------------------------
-- The lexicographical order.
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
{-# ATP definition LT₂ #-}

