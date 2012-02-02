------------------------------------------------------------------------------
-- Totality of Boolean conjunction
------------------------------------------------------------------------------

-- Tested with magda and agda2atp on 15 December 2011.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FOTC.Data.Bool.AndTotality where

open import FOTC.Base
open import FOTC.Data.Bool.Type

------------------------------------------------------------------------------

postulate
  thm : ∀ (P : D → Set) {b}  → (Bool b ∧ P true ∧ P false) → P b
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm #-}

postulate
  thm₁ : ∀ {P : D → Set} {x y z} → Bool x → P y → P z → P (if x then y else z)
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm₁ #-}

-- Typing of the if-then-else.
if-T : ∀ (P : D → Set) {x y z} → Bool x → P y → P z →
       P (if x then y else z)
if-T P {y = y} tB Py Pz = subst P (sym (if-true y)) Py
if-T P {z = z} fB Py Pz = subst P (sym (if-false z)) Pz

_&&_ : D → D → D
x && y = if x then y else false
{-# ATP definition _&&_ #-}

postulate
  &&-Bool : ∀ {x y} → Bool x → Bool y → Bool (x && y)
{-# ATP prove &&-Bool if-T #-}

&&-Bool₁ : ∀ {x y} → Bool x → Bool y → Bool (x && y)
&&-Bool₁ {y = y} tB By = prf
  where
    postulate prf : Bool (true && y)
    {-# ATP prove prf if-T #-}
&&-Bool₁ {y = y} fB By = prf
  where
    postulate prf : Bool (false && y)
    {-# ATP prove prf if-T #-}

&&-Bool₂ : ∀ {x y} → Bool x → Bool y → Bool (x && y)
&&-Bool₂ tB By = if-T Bool tB By fB
&&-Bool₂ fB By = if-T Bool fB By fB
