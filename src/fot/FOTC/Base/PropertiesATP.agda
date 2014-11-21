------------------------------------------------------------------------------
-- FOCT terms properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Base.PropertiesATP where

open import FOTC.Base

------------------------------------------------------------------------------
-- Injective properties

postulate succInjective : ∀ {m n} → succ₁ m ≡ succ₁ n → m ≡ n
{-# ATP prove succInjective #-}

------------------------------------------------------------------------------
-- Discrimination rules

postulate S≢0 : ∀ {n} → succ₁ n ≢ zero
{-# ATP prove S≢0 #-}
