------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality.Type

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- relation _≈N_ is also a pre-fixed point of the functional ≈NatF,
-- i.e.
--
-- ≈NatF _≈N_ ≤ _≈N_ (see FOTC.Data.Conat.Equality.Type).
≈N-pre-fixed :
  ∀ {m n} →
  m ≡ zero ∧ n ≡ zero
    ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈N n') →
  m ≈N n
≈N-pre-fixed h = ≈N-coind R h' h
  where
  R : D → D → Set
  R m n = m ≡ zero ∧ n ≡ zero
            ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈N n')
  {-# ATP definition R #-}

  postulate
    h' : ∀ {m n} → R m n →
         m ≡ zero ∧ n ≡ zero
           ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  {-# ATP prove h' #-}

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R a b = Conat a ∧ Conat b ∧ a ≡ b
  {-# ATP definition R #-}

  postulate
    h₁ : ∀ {a b} → R a b →
         a ≡ zero ∧ b ≡ zero
           ∨ (∃[ a' ] ∃[ b' ] a ≡ succ₁ a' ∧ b ≡ succ₁ b' ∧ R a' b')
  {-# ATP prove h₁ #-}

  postulate h₂ : R n n
  {-# ATP prove h₂ #-}

  postulate ≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
  {-# ATP prove ≡→≈N ≈N-refl #-}
