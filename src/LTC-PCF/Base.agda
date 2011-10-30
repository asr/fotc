------------------------------------------------------------------------------
-- The LTC-PCF base
------------------------------------------------------------------------------

module LTC-PCF.Base where

-- We added to the FOTC base the term
--
-- lam : (D → D) → D
--
-- and it conversion rule.

open import FOTC.Base public

------------------------------------------------------------------------------
-- New terms for LTC

postulate
  lam : (D → D) → D  -- LTC abstraction.

------------------------------------------------------------------------------
-- Conversion rules

-- See the comments in FOTC.Base.

-- Conversion rule for pred.
-- N.B. We don't need this equation in the FOTC.
postulate pred-0 : pred₁ zero ≡ zero
{-# ATP axiom pred-0 #-}

-- Conversion rule for the abstraction and the application.
postulate beta : (f : D → D)(a : D) → lam f · a ≡ f a
{-# ATP axiom beta #-}
