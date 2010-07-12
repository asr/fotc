------------------------------------------------------------------------------
-- Some stuff to be proved
------------------------------------------------------------------------------

module Postulates where

open import LTC.Minimal

open import LTC.Data.Bool

------------------------------------------------------------------------------

postulate
  w&&x&&y&&z≡true→y≡true :
    {b₁ b₂ b₃ b₄ : D} → Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
    b₁ && b₂ && b₃ && b₄ ≡ true → b₃ ≡ true
