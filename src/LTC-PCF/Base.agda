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
  -- fixFO  : D

------------------------------------------------------------------------------
-- Conversion rules

postulate
  -- Conversion rules for pred.
  -- N.B. We don't need this equation in the FOTC.
  pred-0 : pred zero ≡ zero
{-# ATP axiom pred-0 #-}

postulate
  -- Conversion rule for the abstraction and the application.
  beta : (f : D → D)(a : D) → lam f · a ≡ f a
{-# ATP axiom beta #-}

postulate
  -- Conversion rule for the fixed pointed operator.
  fix-f : (f : D → D) → fix f ≡ f (fix  f)
  -- cFixFO : (f : D) → fixFO · f ≡ f · (fixFO · f)
{-# ATP axiom fix-f #-}
