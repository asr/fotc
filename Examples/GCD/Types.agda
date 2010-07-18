------------------------------------------------------------------------------
-- Common types used by the gcd example
------------------------------------------------------------------------------

module Examples.GCD.Types where

open import LTC.Minimal

------------------------------------------------------------------------------
-- TODO: Relocate this function.
¬x≡0∧y≡0 : D → D → Set
¬x≡0∧y≡0 d e = ¬ ((d ≡ zero) ∧ (e ≡ zero))
