------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.By0 where

open import FOTC.Base
open import FOTC.Data.Nat

-- We add 3 to the fixities of the standard library.
infix 7 _∣_

-- References:
--
-- • G. H. Hardy and E. M. Wright. An Introduction to the Theory of
-- Numbers. Oxford University Press, 4th edition, 1975.
--
-- • Donald E. Knuth. The Art of Computer Programming. Volume
-- 1. Fundamental Algorithms. Addison-Wesley Professional, 3rd
-- edition, 1997.

------------------------------------------------------------------------------
-- The relation of divisibility (the symbol is '\mid' not '|')
--
-- It seems there is not agreement about if 0∣0, e.g.
-- • Hardy and Wright 1975, p. 1: 0∤0
-- • Knuth 1977, p. 40: 0∤0
-- • Agda standard library 0.6: 0|0
-- • Coq 8.4: 0∣0
-- • Isabelle 2012: 0∣0

-- In our definition 0∣0, which is used to prove properties of the gcd
-- as it is in GHC ≥ 7.2.1, where gcd 0 0 = 0 (see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).

-- Note that @k@ should be a total natural number.
_∣_ : D → D → Set
m ∣ n = ∃[ k ] N k ∧ n ≡ k * m
{-# ATP definition _∣_ #-}
