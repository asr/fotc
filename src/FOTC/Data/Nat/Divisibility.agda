------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.Divisibility where

open import FOTC.Base

open import FOTC.Data.Nat using ( _*_ ; N )

-- We add 3 to the fixities of the standard library.
infix 7 _∣_

------------------------------------------------------------------------------
-- The relation of divisibility.
-- The symbol is '\mid' not '|'.
-- It seems there is not agreement about if 0∣0, e.g.
-- Coq 8.3: 0∣0
-- Agda standard library, version 0.5: 0|0
-- Hardy and Wright. An introduction to the theory of numbers. 1975. 4ed: 0∤0
--
-- In our definition 0∤0, therefore gcd 0 0 is undefined as it is in
-- GHC (v. 7.0.3) (but see the discussion about it in
-- http://www.haskell.org/pipermail/haskell-cafe/2009-May/060788.html).
_∣_ : D → D → Set
d ∣ e = ¬ (d ≡ zero) ∧ ∃ λ k → N k ∧ e ≡ k * d
{-# ATP definition _∣_ #-}
