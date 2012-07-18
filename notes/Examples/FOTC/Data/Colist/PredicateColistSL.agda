------------------------------------------------------------------------------
-- We could not define the FOTC colists using the Agda machinery for
-- coinductive types.
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Examples.FOTC.Data.Colist.PredicateColistSL where

open import FOTC.Base

open import Coinduction

------------------------------------------------------------------------------

data Colist : D → Set where
  nilCL  : Colist []
  consCL : ∀ x xs → ∞ (Colist xs) → Colist (x ∷ xs)

-- Example (finite colist).
l₁ : Colist (zero ∷ true ∷ [])
l₁ = consCL zero (true ∷ []) (♯ (consCL true [] (♯ nilCL)))

-- Example (infinite colist).
-- zerosCL : Colist {!!}
-- zerosCL = consCL zero {!!} (♯ zerosCL)
