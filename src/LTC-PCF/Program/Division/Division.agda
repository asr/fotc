------------------------------------------------------------------------------
-- Division program
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module define a division program using repeated subtraction
-- (Dybjer 1985).

-- Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

module LTC-PCF.Program.Division.Division where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Version using lambda-abstraction.
-- divh : D → D
-- divh g = lam (λ i → lam (λ j →
--              if (lt i j)
--                then zero
--                else (succ (g · (i ∸ j) · j))))

-- Version using lambda lifting via super-combinators
-- (Hughes. Super-combinators. 1982).

div-helper₁ : D → D → D → D
div-helper₁ i g j = if (i < j) then zero else succ₁ (g · (i ∸ j) · j)
{-# ATP definition div-helper₁ #-}

div-helper₂ : D → D → D
div-helper₂ g i = lam (div-helper₁ i g)
{-# ATP definition div-helper₂ #-}

divh : D → D
divh g = lam (div-helper₂ g)
{-# ATP definition divh #-}

div : D → D → D
div i j = fix divh · i · j
{-# ATP definition div #-}
