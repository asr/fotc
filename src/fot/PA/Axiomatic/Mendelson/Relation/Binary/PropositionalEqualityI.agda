------------------------------------------------------------------------------
-- Axiomatic PA propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEqualityI where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------
-- Identity properties

≈-refl : ∀ {n} → n ≈ n
≈-refl {n} = S₁ (S₅ n) (S₅ n)

≈-sym : ∀ {m n} → m ≈ n → n ≈ m
≈-sym h = S₁ h ≈-refl

≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
≈-trans h = S₁ (≈-sym h)

------------------------------------------------------------------------------
-- Substitution

-- Using Mendelson's axioms we cannot prove

--    a ≈ b    A(x)
--  ----------------- substitution
--         A(x)

-- where A(x) is an arbitrary propositional function, We can prove
-- substitutivity of `_≈_` for the proper functional symbols of the
-- language (`succ`, `add` and `mult`). That is, we can prove (by
-- induction)

--   succCong    : ∀ {m n} → m ≈ n → succ m ≈ succ n
--   +-rightCong : ∀ {m n p} → n ≈ p → m + n ≈ m + p
--   +-leftCong  : ∀ {m n p} → m ≈ n → m + p ≈ n + p
--   *-rightCong : ∀ {m n p} → n ≈ p → m * n ≈ m * p
--   *-leftCong  : ∀ {m n p} → m ≈ n → m * p ≈ n * p

-- The proofs of the above properties are in the `PropertiesI` module.
