------------------------------------------------------------------------------
-- FOTC natural numbers used by the Collatz function

-- (We don't want populate the FOTC library with more FOL axioms)
------------------------------------------------------------------------------

module Draft.FOTC.Program.Collatz.Data.Nat where

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
  /-x≥y : ∀ {m n} → GE m n → m / n ≡ succ (m ∸ n / n)

postulate
  _^_ : D → D → D
  ^-0 : ∀ n →   n ^ zero   ≡ one
  ^-S : ∀ m n → m ^ succ n ≡ m * m ^ n

-- Some predicates
Even : D → Set
Even n = ∃D (λ k → n ≡ two * k)

Odd : D → Set
Odd n = ∃D (λ k → n ≡ two * k + one)
