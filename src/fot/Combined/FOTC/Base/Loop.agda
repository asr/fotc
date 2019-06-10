------------------------------------------------------------------------------
-- FOTC looping (error) combinator
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Base.Loop where

open import Combined.FOTC.Base

------------------------------------------------------------------------------

postulate error : D

-- Conversion rule
--
-- The equation error-eq adds anything to the logic (because
-- reflexivity is already an axiom of equality), therefore we won't
-- add this equation as a first-order logic axiom.
--
-- postulate error-eq : error ≡ error
