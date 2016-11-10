------------------------------------------------------------------------------
-- FOL equality theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.Equality.TheoremsI where

open import FOL.Base

-- Mendelson's [2015] substitution (p. 93).

--   (A7) x = y ⇒ (A(x,x) ⇒ B(x,y)) (substitutivity of equality)

-- Using pattern matching.
biSubst₁ : (A : D → D → Set) → ∀ {x y} → x ≡ y → A x x → A x y
biSubst₁ A refl Axx = Axx

-- Using `subst`.
biSubst₂ : (A : D → D → Set) → ∀ {x y} → x ≡ y → A x x → A x y
biSubst₂ A {x} h Axx = subst (λ z → A x z) h Axx

------------------------------------------------------------------------------
-- References

-- Mendelson, Elliott (2015). Introduction to Mathematical Logic. CRC
-- Press, 6th edition.
