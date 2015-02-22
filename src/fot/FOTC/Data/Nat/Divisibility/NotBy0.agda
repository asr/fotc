------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Nat.Divisibility.NotBy0 where

open import FOTC.Base
open import FOTC.Data.Nat

infix 4 _∣_

------------------------------------------------------------------------------
-- The relation of divisibility (the symbol is '\mid' not '|')
--
-- (See documentation in FOTC.Data.Nat.Divisibility.By0)
--
-- In our definition 0∤0, which is used to prove properties of the gcd
-- as it is in GHC ≤ 7.0.4, where gcd 0 0 = undefined (see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).

-- Note that @k@ should be a total natural number.
_∣_ : D → D → Set
m ∣ n =  (m ≢ zero) ∧ (∃[ k ] N k ∧ n ≡ k * m)
{-# ATP definition _∣_ #-}
