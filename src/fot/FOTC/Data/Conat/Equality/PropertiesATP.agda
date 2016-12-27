------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Conat.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality.Type

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- relation _≈N_ is also a pre-fixed point of the functional ≈-F, i.e.
--
-- ≈-F _≈_ ≤ _≈_ (see FOTC.Data.Conat.Equality.Type).

-- See Issue https://github.com/asr/apia/issues/81 .
≈-inR : D → D → Set
≈-inR m n = m ≡ zero ∧ n ≡ zero
            ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈ n')
{-# ATP definition ≈-inR #-}

≈-in :
  ∀ {m n} →
  m ≡ zero ∧ n ≡ zero
    ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈ n') →
  m ≈ n
≈-in h = ≈-coind ≈-inR h' h
  where
  postulate
    h' : ∀ {m n} → ≈-inR m n →
         m ≡ zero ∧ n ≡ zero
           ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ ≈-inR m' n')
  {-# ATP prove h' #-}

-- See Issue https://github.com/asr/apia/issues/81 .
≈-reflR : D → D → Set
≈-reflR a b = Conat a ∧ Conat b ∧ a ≡ b
{-# ATP definition ≈-reflR #-}

≈-refl : ∀ {n} → Conat n → n ≈ n
≈-refl {n} Cn = ≈-coind ≈-reflR h₁ h₂
  where
  postulate
    h₁ : ∀ {a b} → ≈-reflR a b →
         a ≡ zero ∧ b ≡ zero
           ∨ (∃[ a' ] ∃[ b' ] a ≡ succ₁ a' ∧ b ≡ succ₁ b' ∧ ≈-reflR a' b')
  {-# ATP prove h₁ #-}

  postulate h₂ : ≈-reflR n n
  {-# ATP prove h₂ #-}

  postulate ≡→≈ : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈ n
  {-# ATP prove ≡→≈ ≈-refl #-}
