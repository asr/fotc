------------------------------------------------------------------------------
-- FOTC looping (error) combinator
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Base.Loop where

open import FOTC.Base

------------------------------------------------------------------------------

postulate error : D

-- Conversion rule
--
-- The equation error-eq adds anything to the logic (because
-- reflexivity is already an axiom of equality), therefore we won't
-- add this equation as a first-order logic axiom.
--
-- postulate error-eq : error ≡ error
