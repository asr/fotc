------------------------------------------------------------------------------
-- Mendelson's substitution
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOL.MendelsonSubstATP where

-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

------------------------------------------------------------------------------

-- Mendelson's [2015] substitution (p. 93).

--   (A7) x = y ⇒ (A(x,x) ⇒ B(x,y)) (substitutivity of equality)

postulate mendelsonSubst : (A : D → D → Set) → ∀ {x y} → x ≡ y → A x x → A x y

{-# ATP prove mendelsonSubst #-}

------------------------------------------------------------------------------
-- References

-- Mendelson, Elliott (2015). Introduction to Mathematical Logic. CRC
-- Press, 6th edition.
