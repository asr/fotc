------------------------------------------------------------------------------
-- Well-founded relation on lists based on their structure
------------------------------------------------------------------------------

module FOTC.Data.List.LT-Cons where

open import FOTC.Base

------------------------------------------------------------------------------
-- Well-founded relation on lists based on their structure.
LTC : D → D → Set
LTC xs ys = ∃ (λ a → ys ≡ a ∷ xs)
