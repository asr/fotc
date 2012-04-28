------------------------------------------------------------------------------
-- First-order Peano arithmetic (PA)
------------------------------------------------------------------------------

module PA.README where

-- Two formalizations of first-order Peano aritmetic using:

-- • Agda postulates for the non-logical constants and the Peano's
--   axioms, using axioms based on the propositional equality (see,
--   for example, (Machover 1996, p. 263), (Hájek and Pudlák 1998,
--   p. 28).

-- • Agda data types and primitive recursive functions for addition and
--   multiplication.

-- References:
--
-- • Moshé Machover. Set theory, logic and their limitations. Cambridge
--   University Press, 1996.
--
-- • Petr Hájek and Pavel Pudlák. Metamathematics of First-Order
--   Arithmetic. Springer, 1998. 2nd printing.

------------------------------------------------------------------------------
-- Axiomatic PA

-- The axioms
open import PA.Axiomatic.Standard.Base

-- Some properties
open import PA.Axiomatic.Standard.PropertiesATP
open import PA.Axiomatic.Standard.PropertiesI

------------------------------------------------------------------------------
-- Inductive PA

-- Inductive definitions
open import PA.Inductive.Base

-- Some properties
open import PA.Inductive.Properties
open import PA.Inductive.PropertiesATP
open import PA.Inductive.PropertiesI

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.PropertiesByInductionATP
open import PA.Inductive.PropertiesByInductionI
