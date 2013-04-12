------------------------------------------------------------------------------
-- FOCT terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.PropertiesATP where

open import FOTC.Base

------------------------------------------------------------------------------

postulate S≢0 : ∀ {n} → succ₁ n ≢ zero
{-# ATP prove S≢0 #-}
