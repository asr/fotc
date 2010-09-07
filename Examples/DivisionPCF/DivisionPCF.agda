------------------------------------------------------------------------------
-- Division program
------------------------------------------------------------------------------

-- This module define a division program using repeated subtraction
-- (Dybjer 1985).

-- Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

module Examples.DivisionPCF.DivisionPCF where

open import LTC.Minimal

open import LTC-PCF.DataPCF.NatPCF                 using ( _-_ )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( _<_ )

------------------------------------------------------------------------------

-- Version using lambda-abstraction.
-- divh : D → D
-- divh g = lam (λ i → lam (λ j →
--              if (lt i j)
--                then zero
--                else (succ (g ∙ (i - j) ∙ j))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

div-aux₁ : D → D → D → D
div-aux₁ i g j = if (i < j) then zero else (succ (g ∙ (i - j) ∙ j))
{-# ATP definition div-aux₁ #-}

div-aux₂ : D → D → D
div-aux₂ g i = lam (div-aux₁ i g)
{-# ATP definition div-aux₂ #-}

divh : D → D
divh g = lam (div-aux₂ g)
{-# ATP definition divh #-}

div : D → D → D
div i j = fix divh ∙ i ∙ j
{-# ATP definition div #-}
