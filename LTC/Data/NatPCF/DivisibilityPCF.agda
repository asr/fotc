------------------------------------------------------------------------------
-- The relation of divisibility on partial natural numbers
------------------------------------------------------------------------------

module LTC.Data.NatPCF.DivisibilityPCF where

open import LTC.Minimal

open import LTC.Data.NatPCF

infix 4 _∣_

------------------------------------------------------------------------------
-- It seems there is not agreement about if 0∣0 (e.g. see Coq definition
-- (0∣0), Agda library (0∤0), or MathWorld (0∤0)). At the moment, in our
-- definition 0∤0.

-- data _∣_ : D → D → Set where
--   ∣-i : {m n : D} → ∃D (λ k → n ≡ k * succ m) → succ m ∣ n
-- {-# ATP hint ∣-i #-}

-- The relation of divisibility.
-- The symbol is '\mid' not '|'.
-- What about change '∃' by '(k : D)' (e.g. the standard library uses it)?
_∣_ : D → D → Set
d ∣ e = ¬ (d ≡ zero) ∧ ∃D (λ k → (N k) ∧ (e ≡ k * d))
{-# ATP definition _∣_ #-}
