------------------------------------------------------------------------------
-- FOCT terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.PropertiesATP where

open import FOTC.Base
open FOTC.Base.BList

------------------------------------------------------------------------------
-- Congruence properties

postulate succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
{-# ATP prove succCong #-}

postulate predCong : ∀ {m n} → m ≡ n → pred₁ m ≡ pred₁ n
{-# ATP prove predCong #-}

------------------------------------------------------------------------------
-- Injective properties

postulate succInjective : ∀ {m n} → succ₁ m ≡ succ₁ n → m ≡ n
{-# ATP prove succInjective #-}

postulate ∷-injective : ∀ {x y xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
{-# ATP prove ∷-injective #-}
