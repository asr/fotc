------------------------------------------------------------------------------
-- Induction principles for Tree and Forest
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Yves Bertot and Pierre Castéran. Interactive Theorem Proving and
--   Program Development. Coq'Art: The Calculus of Inductive
--   Constructions. Springer, 2004

module FOT.FOTC.Program.Mirror.Induction.InductionPrinciples where

open import FOTC.Base
open import FOTC.Program.Mirror.Type hiding ( Forest-ind ; Tree-ind )

------------------------------------------------------------------------------
-- These induction principles *not cover* the mutual structure of the
-- types Tree and Rose (Bertot and Casterán, 2004, p. 401).

-- Induction principle for Tree.
Tree-ind : (A : D → Set) →
           (∀ d {ts} → Forest ts → A (node d ts)) →
           ∀ {t} → Tree t → A t
Tree-ind A h (tree d Fts) = h d Fts

-- Induction principle for Forest.
Forest-ind : (A : D → Set) →
             A [] →
             (∀ {t ts} → Tree t → Forest ts → A ts → A (t ∷ ts)) →
             ∀ {ts} → Forest ts → A ts
Forest-ind A Anil h fnil           = Anil
Forest-ind A Anil h (fcons Tt Fts) = h Tt Fts (Forest-ind A Anil h Fts)
