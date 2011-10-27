------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Inequalities where

open import LTC-PCF.Base

------------------------------------------------------------------------------
-- Version using lambda-abstraction.
-- lth : D → D
-- lth lt = lam (λ m → lam (λ n →
--               if (isZero n) then false
--                  else (if (isZero m) then true
--                           else (lt · (pred m) · (pred n)))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

-- Agda changes the evaluation behaviour (we have not identified in
-- which particular case) after the patch
--
-- Thu Sep 15 14:15:05 COT 2011  ulfn@chalmers.se
-- * fixed issue 365: different evaluation behaviour for point-free and pointed style
--
-- Therefore, to avoid the new evaluation we use an abstrac block
abstract
  <-helper₁ : D → D → D → D
  <-helper₁ d lt e = if (iszero₁ e)
                        then false
                        else (if (iszero₁ d)
                                 then true
                                 else (lt · (pred₁ d) · (pred₁ e)))
  {-# ATP definition <-helper₁ #-}

  <-helper₂ : D → D → D
  <-helper₂ lt d = lam (<-helper₁ d lt)
  {-# ATP definition <-helper₂ #-}

  <-h : D → D
  <-h lt = lam (<-helper₂ lt)
  {-# ATP definition <-h #-}

  -- Because we cannot get the propositional equality from the
  -- definitional equality outside of an abstract block, we use the
  -- following auxiliaries theorems

  <-h-≡ : ∀ lt → <-h lt ≡ lam (<-helper₂ lt)
  <-h-≡ lt = refl

  <-helper₂-≡ : ∀ lt d → <-helper₂ lt d ≡ lam (<-helper₁ d lt)
  <-helper₂-≡ lt d = refl

  <-helper₁-≡ : ∀ d lt e → <-helper₁ d lt e ≡
                           if (iszero₁ e)
                              then false
                              else (if (iszero₁ d)
                                       then true
                                       else (lt · (pred₁ d) · (pred₁ e)))
  <-helper₁-≡ d lt e = refl

_<_ : D → D → D
d < e = fix <-h · d · e
{-# ATP definition _<_ #-}

_≤_ : D → D → D
d ≤ e = d < succ₁ e
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
