------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.NotBy0 where

open import FOTC.Base
open import FOTC.Data.Nat

-- We add 3 to the fixities of the standard library.
infix 7 _∣_

------------------------------------------------------------------------------
-- The relation of divisibility.
-- The symbol is '\mid' not '|'.
-- It seems there is not agreement about if 0∣0, e.g.
-- * Agda standard library, version 0.5: 0|0
-- * Coq 8.3pl2: 0∣0
-- * Hardy and Wright. An introduction to the theory of numbers. 1975. 4ed: 0∤0
-- * Isabelle, version Isabelle2011: 0∣0
--
-- In our definition 0∤0, which is used to prove properties of the gcd
-- as it is in GHC ≤ 7.0.4, where @gcd 0 0 = undefined@ (see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).
_∣_ : D → D → Set
m ∣ n = ¬ (m ≡ zero) ∧ (∃[ k ] N k ∧ n ≡ k * m)
{-# ATP definition _∣_ #-}
