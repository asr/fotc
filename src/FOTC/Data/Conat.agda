------------------------------------------------------------------------------
-- Coinductive natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Conat where

open import FOTC.Base

-- The FOTC Coinductive natural numbers type.
open import FOTC.Data.Conat.Type public

------------------------------------------------------------------------------

postulate
  ω    : D
  ω-eq : ω ≡ succ₁ ω
