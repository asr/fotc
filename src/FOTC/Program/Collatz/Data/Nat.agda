------------------------------------------------------------------------------
-- FOTC natural numbers (added for the Collatz function example)

-- (We don't want populate the FOTC library with more FOL axioms)
------------------------------------------------------------------------------

module FOTC.Program.Collatz.Data.Nat where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

infixr 12 _^_
infixl 10 _/_

------------------------------------------------------------------------------

postulate
  _/_   : D → D → D
  /-x<y : ∀ {m n} → LT m n → m / n ≡ zero
  /-x≥y : ∀ {m n} → GE m n → m / n ≡ succ ((m ∸ n) / n)
{-# ATP axiom /-x<y #-}
{-# ATP axiom /-x≥y #-}

postulate
  _^_ : D → D → D
  ^-0 : ∀ n →   n ^ zero   ≡ one
  ^-S : ∀ m n → m ^ succ n ≡ m * m ^ n
{-# ATP axiom ^-0 #-}
{-# ATP axiom ^-S #-}

-- Some predicates

Even : D → Set
Even n = ∃ λ k → n ≡ two * k

Odd : D → Set
Odd n = ∃ λ k → n ≡ two * k + one
