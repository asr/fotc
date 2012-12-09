------------------------------------------------------------------------------
-- FOCT terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.PropertiesATP where

open import FOTC.Base

------------------------------------------------------------------------------
-- Congruence properties

postulate ·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
{-# ATP prove ·-leftCong #-}

postulate ·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
{-# ATP prove ·-rightCong #-}

postulate ·-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a · c ≡ b · d
{-# ATP prove ·-cong #-}

postulate succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
{-# ATP prove succCong #-}

postulate predCong : ∀ {m n} → m ≡ n → pred₁ m ≡ pred₁ n
{-# ATP prove predCong #-}

------------------------------------------------------------------------------
-- Injective properties

postulate succInjective : ∀ {m n} → succ₁ m ≡ succ₁ n → m ≡ n
{-# ATP prove succInjective #-}

------------------------------------------------------------------------------

postulate S≢0 : ∀ {n} → succ₁ n ≢ zero
{-# ATP prove S≢0 #-}
