------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat.Divisibility.By0 where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data.Nat.Divisibility).
infix 7 _∣_

------------------------------------------------------------------------------
-- The relation of divisibility (the symbol is '\mid' not '|')
--
-- (See documentation in FOTC.Data.Nat.Divisibility.By0)
--
-- In our definition 0∣0, which is used to prove properties of the gcd
-- as it is in GHC ≥ 7.2.1, where gcd 0 0 = 0 (see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).

-- Note that @k@ should be a total natural number.
_∣_ : D → D → Set
m ∣ n = ∃[ k ] N k ∧ n ≡ k * m
