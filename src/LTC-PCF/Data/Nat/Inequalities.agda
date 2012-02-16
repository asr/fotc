------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

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
  <-helper₁ m lt n = if (iszero₁ n)
                        then false
                        else (if (iszero₁ m)
                                 then true
                                 else (lt · (pred₁ m) · (pred₁ n)))
  {-# ATP definition <-helper₁ #-}

  <-helper₂ : D → D → D
  <-helper₂ lt n = lam (<-helper₁ n lt)
  {-# ATP definition <-helper₂ #-}

  <-h : D → D
  <-h lt = lam (<-helper₂ lt)
  {-# ATP definition <-h #-}

  -- Because we cannot get the propositional equality from the
  -- definitional equality outside of an abstract block, we use the
  -- following auxiliaries theorems

  <-h-≡ : ∀ lt → <-h lt ≡ lam (<-helper₂ lt)
  <-h-≡ lt = refl

  <-helper₂-≡ : ∀ lt n → <-helper₂ lt n ≡ lam (<-helper₁ n lt)
  <-helper₂-≡ lt n = refl

  <-helper₁-≡ : ∀ m lt n → <-helper₁ m lt n ≡
                           if (iszero₁ n)
                              then false
                              else (if (iszero₁ m)
                                       then true
                                       else (lt · (pred₁ m) · (pred₁ n)))
  <-helper₁-≡ m lt n = refl

_<_ : D → D → D
m < n = fix <-h · m · n
{-# ATP definition _<_ #-}

_≤_ : D → D → D
m ≤ n = m < succ₁ n
{-# ATP definition _≤_ #-}

_>_ : D → D → D
m > n = n < m
{-# ATP definition _>_ #-}

_≥_ : D → D → D
m ≥ n = n ≤ m
{-# ATP definition _≥_ #-}

------------------------------------------------------------------------
-- The data types

GT : D → D → Set
GT m n = m > n ≡ true
{-# ATP definition GT #-}

NGT : D → D → Set
NGT m n = m > n ≡ false
{-# ATP definition NGT #-}

LT : D → D → Set
LT m n = m < n ≡ true
{-# ATP definition LT #-}

NLT : D → D → Set
NLT m n = m < n ≡ false
{-# ATP definition NLT #-}

LE : D → D → Set
LE m n = m ≤ n ≡ true
{-# ATP definition LE #-}

NLE : D → D → Set
NLE m n = m ≤ n ≡ false
{-# ATP definition NLE #-}

GE : D → D → Set
GE m n = m ≥ n ≡ true
{-# ATP definition GE #-}

NGE : D → D → Set
NGE m n = m ≥ n ≡ false
{-# ATP definition NGE #-}

------------------------------------------------------------------------------
-- The lexicographical order.
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
{-# ATP definition LT₂ #-}
