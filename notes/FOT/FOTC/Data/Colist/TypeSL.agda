------------------------------------------------------------------------------
-- We could not define the FOTC colists using the Agda machinery for
-- co-inductive types.
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Colist.TypeSL where

open import Coinduction

open import FOTC.Base
open import FOTC.Base.List

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
