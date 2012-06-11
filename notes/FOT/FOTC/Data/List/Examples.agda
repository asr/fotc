------------------------------------------------------------------------------
-- Lists examples
------------------------------------------------------------------------------

-- Tested with FOT on 11 June 2012.

module FOT.FOTC.Data.List.Examples where

open import FOTC.Base

open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.List.Type

------------------------------------------------------------------------------

l₁ : List (true ∷ false ∷ [])
l₁ = consL true (consL false nilL)

l₂ : List (zero ∷ one ∷ two ∷ [])
l₂ = consL zero (consL one (consL two nilL))
