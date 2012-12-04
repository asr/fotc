------------------------------------------------------------------------------
-- FOTC looping combinator
------------------------------------------------------------------------------

module FOTC.Base.Loop where

open import FOTC.Base

------------------------------------------------------------------------------

postulate loop : D

-- Conversion rule
--
-- The equation loop-eq adds anything to the logic (because
-- reflexivity is already an axiom of equality), therefore we won't
-- add this equation as a first-order logic axiom.
--
-- postulate loop-eq : loop ≡ loop
