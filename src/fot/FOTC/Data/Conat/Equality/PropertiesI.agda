------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Herbert P. Sander. A logic of functional programs with an
--   application to concurrency. PhD thesis, Chalmers University of
--   Technology and University of Gothenburg, Department of Computer
--   Sciences, 1992.

module FOTC.Data.Conat.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality

------------------------------------------------------------------------------

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind R prf₁ prf₂
  where
  R : D → D → Set
  R a b = Conat a ∧ Conat b ∧ a ≡ b

  prf₁ : ∀ {a b} → R a b →
         a ≡ zero ∧ b ≡ zero
         ∨ (∃[ a' ] ∃[ b' ] a ≡ succ₁ a' ∧ b ≡ succ₁ b' ∧ R a' b')
  prf₁ (Ca , Cb , refl) with Conat-unf Ca
  ... | inj₁ prf              = inj₁ (prf , prf)
  ... | inj₂ (a' , prf , Ca') = inj₂ (a' , a' , prf , prf , (Ca' , Ca' , refl))

  prf₂ : Conat n ∧ Conat n ∧ n ≡ n
  prf₂ = Cn , Cn , refl

≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
≡→≈N h _ refl = ≈N-refl h
