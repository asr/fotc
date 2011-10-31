------------------------------------------------------------------------------
-- The LTC-PCF base
------------------------------------------------------------------------------

module LTC-PCF.Base where

-- We added to the FOTC base the following terms
--
-- lam : (D → D) → D
-- fix : D
--
-- and their conversion rules

open import FOTC.Base public

------------------------------------------------------------------------------
-- New terms for LTC

postulate
  lam : (D → D) → D  -- LTC abstraction.
  fix : D            -- LTC fixed point operator.

------------------------------------------------------------------------------
-- Definitions for LTC

abstract
  fix₁ : (D → D) → D
  fix₁ f = fix · lam f

------------------------------------------------------------------------------
-- Conversion rules

-- See the comments to the conversion rules in FOTC.Base.

-- Conversion rule for pred.
-- N.B. We don't need this equation in the FOTC.
postulate pred-0 : pred₁ zero ≡ zero
{-# ATP axiom pred-0 #-}

-- Conversion rule for the abstraction and the application.
postulate beta : (f : D → D)(a : D) → lam f · a ≡ f a
{-# ATP axiom beta #-}

-- Conversion rule for the fixed pointed operator.
postulate fix-f : (f : D → D) → fix₁ f ≡ f (fix₁ f)
{-# ATP axiom fix-f #-}
