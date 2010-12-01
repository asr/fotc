------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Inequalities where

open import LTC.Base

------------------------------------------------------------------------------
-- Version using lambda-abstraction.
-- lth : D → D
-- lth lt = lam (λ m → lam (λ n →
--               if (isZero n) then false
--                  else (if (isZero m) then true
--                           else (lt ∙ (pred m) ∙ (pred n)))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

<-aux₁ : D → D → D → D
<-aux₁ d lt e = if (isZero e)
                   then false
                   else (if (isZero d)
                            then true
                            else (lt ∙ (pred d) ∙ (pred e)))
{-# ATP definition <-aux₁ #-}

<-aux₂ : D → D → D
<-aux₂ lt d = lam (<-aux₁ d lt)
{-# ATP definition <-aux₂ #-}

<-h : D → D
<-h lt = lam (<-aux₂ lt)
{-# ATP definition <-h #-}

_<_ : D → D → D
d < e = fix <-h ∙ d ∙ e
{-# ATP definition _<_ #-}

_≤_ : D → D → D
d ≤ e = d < succ e
{-# ATP definition _≤_ #-}

_>_ : D → D → D
d > e = e < d
{-# ATP definition _>_ #-}

_≥_ : D → D → D
d ≥ e = e ≤ d
{-# ATP definition _≥_ #-}

------------------------------------------------------------------------
-- The data types

GT : D → D → Set
GT d e = d > e ≡ true
{-# ATP definition GT #-}

NGT : D → D → Set
NGT d e = d > e ≡ false
{-# ATP definition NGT #-}

LT : D → D → Set
LT d e = d < e ≡ true
{-# ATP definition LT #-}

NLT : D → D → Set
NLT d e = d < e ≡ false
{-# ATP definition NLT #-}

LE : D → D → Set
LE d e = d ≤ e ≡ true
{-# ATP definition LE #-}

NLE : D → D → Set
NLE d e = d ≤ e ≡ false
{-# ATP definition NLE #-}

GE : D → D → Set
GE d e = d ≥ e ≡ true
{-# ATP definition GE #-}

NGE : D → D → Set
NGE d e = d ≥ e ≡ false
{-# ATP definition NGE #-}

------------------------------------------------------------------------------
-- The lexicographical order.
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
{-# ATP definition LT₂ #-}
