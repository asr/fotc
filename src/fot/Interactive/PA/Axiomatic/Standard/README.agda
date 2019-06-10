------------------------------------------------------------------------------
-- First-order Peano arithmetic
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.PA.Axiomatic.Standard.README where

-- Formalization of first-order Peano arithmetic using Agda postulates
-- for the non-logical constants and the Peano's axioms, and using
-- axioms based on the propositional equality (see, for example,
-- (Machover 1996, p. 263), (Hájek and Pudlák 1998, p. 28).

------------------------------------------------------------------------------
-- The axioms
open import Interactive.PA.Axiomatic.Standard.Base

-- Some properties
open import Interactive.PA.Axiomatic.Standard.Properties

------------------------------------------------------------------------------
-- References
--
-- Machover, Moshé (1996). Set theory, Logic and their
-- Limitations. Cambridge University Press.

-- Hájek, Petr and Pudlák, Pavel (1998). Metamathematics of
-- First-Order Arithmetic. 2nd printing. Springer.
