------------------------------------------------------------------------
-- The FOTC streams type
------------------------------------------------------------------------

module Draft.FOTC.Data.Stream.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC stream type.
postulate
  Stream : D → Set
  consS  : ∀ {x xs} → Stream xs → Stream (x ∷ xs)
