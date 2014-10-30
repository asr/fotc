------------------------------------------------------------------------------
-- Totality of Boolean conjunction
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types                    #-}
{-# OPTIONS --no-universe-polymorphism          #-}
{-# OPTIONS --schematic-propositional-functions #-}
{-# OPTIONS --without-K                         #-}

module FOT.FOTC.Data.Bool.AndTotality where

open import FOTC.Base
open import FOTC.Data.Bool.Type

------------------------------------------------------------------------------

postulate thm : (A : D → Set) → ∀ {b} → (Bool b ∧ A true ∧ A false) → A b
-- Because the ATPs don't handle induction, them cannot prove the
-- induction principle for Bool.
-- {-# ATP prove thm #-}

postulate
  thm₁ : {A : D → Set} → ∀ {x y z} → Bool x → A y → A z → A (if x then y else z)
-- Because the ATPs don't handle induction, them cannot prove this postulate.
-- {-# ATP prove thm₁ #-}

-- Typing of the if-then-else.
if-T : (A : D → Set) → ∀ {x y z} → Bool x → A y → A z →
       A (if x then y else z)
if-T A {y = y} btrue  Ay Az = subst A (sym (if-true y)) Ay
if-T A {z = z} bfalse Ay Az = subst A (sym (if-false z)) Az

_&&_ : D → D → D
x && y = if x then y else false
{-# ATP definition _&&_ #-}

postulate &&-Bool : ∀ {x y} → Bool x → Bool y → Bool (x && y)
{-# ATP prove &&-Bool if-T #-}

&&-Bool₁ : ∀ {x y} → Bool x → Bool y → Bool (x && y)
&&-Bool₁ {y = y} btrue By = prf
  where
    postulate prf : Bool (true && y)
    {-# ATP prove prf if-T #-}
&&-Bool₁ {y = y} bfalse By = prf
  where
    postulate prf : Bool (false && y)
    {-# ATP prove prf if-T #-}

&&-Bool₂ : ∀ {x y} → Bool x → Bool y → Bool (x && y)
&&-Bool₂ btrue  By = if-T Bool btrue By bfalse
&&-Bool₂ bfalse By = if-T Bool bfalse By bfalse
