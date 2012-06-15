------------------------------------------------------------------------------
-- Totality of Boolean conjunction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 11 June 2012.

module FOT.FOTC.Data.Bool.AndTotality where

open import FOTC.Base
open import FOTC.Data.Bool.Type

------------------------------------------------------------------------------

postulate
  thm : (A : D → Set) → ∀ {b} → (Bool b ∧ A true ∧ A false) → A b
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm #-}

postulate
  thm₁ : {A : D → Set} → ∀ {x y z} → Bool x → A y → A z → A (if x then y else z)
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm₁ #-}

-- Typing of the if-then-else.
if-T : (A : D → Set) → ∀ {x y z} → Bool x → A y → A z →
       A (if x then y else z)
if-T A {y = y} tB Ay Az = subst A (sym (if-true y)) Ay
if-T A {z = z} fB Ay Az = subst A (sym (if-false z)) Az

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
