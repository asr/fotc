{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 15 June 2012.

module Issues.Agda365 where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EquationsI
open import LTC-PCF.Data.Nat.PropertiesI

------------------------------------------------------------------------------

-- After the Agda patch

-- Thu Sep 15 14:15:05 COT 2011  ulfn@chalmers.se
--  * fixed issue 365: different evaluation behaviour for point-free and pointed style

-- we get the error

-- $ agda2atp -inotes -isrc notes/Issues/Agda365.agda
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/FOL/Translation/Terms.hs:557

-- because we don't translate the Agda internal λ-terms. I am keeping
-- this example as an possible test case for the translation of the
-- Agda internal lambda terms.

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → LE m n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn = prf (x≤y→y∸x+x≡y Nm Nn m≤n)
  where
  postulate m≤n : LE m n
  {-# ATP prove m≤n <-SS #-}

  postulate prf : (n ∸ m) + m ≡ n → (succ₁ n ∸ succ₁ m) + succ₁ m ≡ succ₁ n
  {-# ATP prove prf +-comm ∸-N +-Sx ∸-SS <-SS #-}
-- This is an incomplete case which does not matter.
x≤y→y∸x+x≡y {m} {n} Nm Nn m≤n = whatever
  where
  postulate whatever : n ∸ m + m ≡ n
