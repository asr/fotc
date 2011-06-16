------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Divisibility.NotBy0 where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat

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
-- In our definition 0∤0, which is used to prove that gcd 0 0 is
-- undefined as it is in GHC 7.0.3 (but see
-- http://hackage.haskell.org/trac/ghc/ticket/3304).
_∣_ : D → D → Set
d ∣ e = ¬ (d ≡ zero) ∧ ∃ λ k → N k ∧ e ≡ k * d
{-# ATP definition _∣_ #-}
