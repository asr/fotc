------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.Divisibility.By0 where

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
--
-- In our definition 0∣0, which is used to prove that gcd 0 0 = 0 as
-- it is in GHC HEAD (7.1.20110615) (see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).
_∣_ : D → D → Set
d ∣ e = ∃ λ k → N k ∧ e ≡ k * d
{-# ATP definition _∣_ #-}
