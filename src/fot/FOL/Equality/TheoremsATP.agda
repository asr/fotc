------------------------------------------------------------------------------
-- FOL equality theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.Equality.TheoremsATP where

open import FOL.Base

-- Mendelson's [2015] substitution (p. 93).

--   (A7) x = y ⇒ (A(x,x) ⇒ B(x,y)) (substitutivity of equality)

postulate biSubst : (A : D → D → Set) → ∀ {x y} → x ≡ y → A x x → A x y

{-# ATP prove biSubst #-}

------------------------------------------------------------------------------
-- References

-- Mendelson, Elliott (2015). Introduction to Mathematical Logic. CRC
-- Press, 6th edition.
