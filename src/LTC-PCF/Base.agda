------------------------------------------------------------------------------
-- The LTC-PCF base
------------------------------------------------------------------------------

module LTC-PCF.Base where

-- We added to the FOTC base the following higher-order terms
-- lam : (D → D) → D
-- fix : (D → D) → D
-- and their conversion rules

open import FOTC.Base public

------------------------------------------------------------------------------
-- New terms for LTC

postulate
  -- LTC abstraction.
  lam : (D → D) → D

  -- LTC fixed point operator.
  fix : (D → D) → D

------------------------------------------------------------------------------
-- Conversion rules

-- Conversion rules for pred.
-- N.B. We don't need this equation in the FOTC.
postulate pred-0 : pred zero ≡ zero
{-# ATP axiom pred-0 #-}

-- Conversion rule for the abstraction and the application.
postulate beta : (f : D → D)(a : D) → lam f · a ≡ f a
{-# ATP axiom beta #-}

-- Conversion rule for the fixed pointed operator.
postulate fix-f : (f : D → D) → fix f ≡ f (fix  f)
{-# ATP axiom fix-f #-}
