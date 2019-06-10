------------------------------------------------------------------------------
-- Induction principles for Tree and Forest
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Program.Mirror.Induction.InductionPrinciples where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Program.Mirror.Type

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
Forest-ind A A[] h fnil           = A[]
Forest-ind A A[] h (fcons Tt Fts) = h Tt Fts (Forest-ind A A[] h Fts)

------------------------------------------------------------------------------
-- References
--
-- Bertot, Yves and Castéran, Pierre (2004). Interactive Theorem
-- Proving and Program Development. Coq’Art: The Calculus of Inductive
-- Constructions. Springer.
