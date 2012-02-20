------------------------------------------------------------------------------
-- Axiomatic PA propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEqualityI where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------
-- Identity properties

≐-refl : ∀ {n} → n ≐ n
≐-refl {n} = S₁ (S₅ n) (S₅ n)
{-# ATP hint ≐-refl #-}

≐-sym : ∀ {m n} → m ≐ n → n ≐ m
≐-sym h = S₁ h ≐-refl
{-# ATP hint ≐-sym #-}

≐-trans : ∀ {m n o} → m ≐ n → n ≐ o → m ≐ o
≐-trans h = S₁ (≐-sym h)
{-# ATP hint ≐-trans #-}
