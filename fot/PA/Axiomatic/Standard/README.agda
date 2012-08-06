------------------------------------------------------------------------------
-- First-order Peano arithmetic
------------------------------------------------------------------------------

module PA.Axiomatic.Standard.README where

-- Formalization of first-order Peano aritmetic using Agda postulates
-- for the non-logical constants and the Peano's axioms, and using
-- axioms based on the propositional equality (see, for example,
-- (Machover 1996, p. 263), (Hájek and Pudlák 1998, p. 28).

-- References:
--
-- • Moshé Machover. Set theory, logic and their limitations. Cambridge
--   University Press, 1996.
--
-- • Petr Hájek and Pavel Pudlák. Metamathematics of First-Order
--   Arithmetic. Springer, 1998. 2nd printing.

------------------------------------------------------------------------------
-- The axioms
open import PA.Axiomatic.Standard.Base

-- Some properties
open import PA.Axiomatic.Standard.PropertiesATP
open import PA.Axiomatic.Standard.PropertiesI
