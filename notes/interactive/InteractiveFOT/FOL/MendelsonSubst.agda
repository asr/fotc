------------------------------------------------------------------------------
-- Mendelson's substitution
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOL.MendelsonSubst where

-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

------------------------------------------------------------------------------

-- Mendelson's [2015] substitution (p. 93).

--   (A7) x = y ⇒ (A(x,x) ⇒ B(x,y)) (substitutivity of equality)

-- Using pattern matching.
mendelsonSubst : (A : D → D → Set) → ∀ {x y} → x ≡ y → A x x → A x y
mendelsonSubst A refl Axx = Axx

-- From `subst` to Mendelson substitution.
subst→mendelsonSubst : (A : D → D → Set) → ∀ {x y} → x ≡ y → A x x → A x y
subst→mendelsonSubst A {x} = subst (λ z → A x z)

-- From Mendelson substitution to `subst`.
mendelsonSubst→subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
mendelsonSubst→subst A = mendelsonSubst (λ _ → A)

------------------------------------------------------------------------------
-- References

-- Mendelson, Elliott (2015). Introduction to Mathematical Logic. CRC
-- Press, 6th edition.
