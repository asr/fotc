------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Nat.Divisibility.By0 where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat

infix 4 _∣_

------------------------------------------------------------------------------
-- The relation of divisibility (the symbol is '\mid' not '|')
--
-- It seems there is not agreement about if 0∣0:
--
-- Hardy and Wright 1975, p. 1: 0∤0
--
-- Knuth 1977, p. 40: 0∤0
--
-- Agda standard library 0.8.1: 0|0
--
-- Coq 8.4pl4: 0∣0
--
-- Isabelle2014: 0∣0

-- In our definition 0∣0, which is used to prove properties of the gcd
-- as it is in GHC ≥ 7.2.1, where gcd 0 0 = 0 (see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).

-- Note that @k@ should be a total natural number.
_∣_ : D → D → Set
m ∣ n = ∃[ k ] N k ∧ n ≡ k * m

------------------------------------------------------------------------------
-- References:
--
-- Hardy, G. H. and Wright, E. M. (1975). An Introduction to the
-- Theory of Numbers. 4th ed. Oxford University Press.
--
-- Knuth, Donald E. (1997). The Art of Computer Programming. 3rd
-- ed. Vol. 1. Fundamental Algorithms. Addison-Wesley Professional.
