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

module FOTC.Data.Conat.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R a b = Conat a ∧ Conat b ∧ a ≡ b
  {-# ATP definition R #-}

  postulate
    h₁ : ∀ {a b} → R a b →
         a ≡ zero ∧ b ≡ zero
         ∨ (∃ (λ a' → ∃ (λ b' → R a' b' ∧ a ≡ succ₁ a' ∧ b ≡ succ₁ b')))
  {-# ATP prove h₁ #-}

  postulate h₂ : Conat n ∧ Conat n ∧ n ≡ n
  {-# ATP prove h₂ #-}

≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
≡→≈N h _ refl = ≈N-refl h

-- Adapted from (Sander 1992, p. 58).
stream-length : ∀ {xs} → Stream xs → length xs ≈N ∞
stream-length {xs} Sxs = ≈N-coind _R_ h₁ h₂
  where
  _R_ : D → D → Set
  m R n = m ≡ zero ∧ n ≡ zero ∨ (∃[ ys ] Stream ys ∧ m ≡ length ys ∧ n ≡ ∞)
  {-# ATP definition _R_ #-}

  postulate
    h₁ : ∀ {m n} → m R n →
         m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m' R n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n')
  {-# ATP prove h₁ #-}

  postulate h₂ : length xs R ∞
  {-# ATP prove h₂ #-}
