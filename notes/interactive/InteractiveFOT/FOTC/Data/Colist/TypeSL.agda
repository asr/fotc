------------------------------------------------------------------------------
-- We could not define the FOTC colists using the Agda machinery for
-- co-inductive types.
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module InteractiveFOT.FOTC.Data.Colist.TypeSL where

open import Codata.Musical.Notation

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List

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
