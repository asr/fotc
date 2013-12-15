------------------------------------------------------------------------------
-- First-order Peano arithmetic
------------------------------------------------------------------------------

module PA.Axiomatic.Standard.README where

-- Formalization of first-order Peano arithmetic using Agda postulates
-- for the non-logical constants and the Peano's axioms, and using
-- axioms based on the propositional equality (see, for example,
-- (Machover 1996, p. 263), (Hájek and Pudlák 1998, p. 28).

------------------------------------------------------------------------------
-- The axioms
open import PA.Axiomatic.Standard.Base

-- Some properties
open import PA.Axiomatic.Standard.PropertiesATP
open import PA.Axiomatic.Standard.PropertiesI

------------------------------------------------------------------------------
-- References:
--
-- • Machover, Moshé (1996). Set theory, Logic and their
--   Limitations. Cambridge University Press.

-- • Hájek, Petr and Pudlák, Pavel (1998). Metamathematics of
--   First-Order Arithmetic. 2nd printing. Springer.
