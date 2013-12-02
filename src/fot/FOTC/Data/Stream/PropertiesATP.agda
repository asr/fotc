------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Stream predicate is also a pre-fixed point of the functional
-- StreamF, i.e.
--
-- StreamF Stream ≤ Stream (see FOTC.Data.Stream.Type).
Stream-pre-fixed : ∀ {xs} →
                   (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs') →
                   Stream xs
Stream-pre-fixed {xs} h = Stream-coind A h' refl
  where
  A : D → Set
  A ws = ws ≡ ws
  {-# ATP definition A #-}

  postulate h' : A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  {-# ATP prove h' #-}

postulate tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove tailS #-}

streamLength : ∀ {xs} → Stream xs → length xs ≈N ∞
streamLength {xs} Sxs = ≈N-coind R h refl
  where
  R : D → D → Set
  R m n = m ≡ m
  {-# ATP definition R #-}

  postulate
    h : R (length xs) ∞ → length xs ≡ zero ∧ ∞ ≡ zero
          ∨ (∃[ m' ] ∃[ n' ] length xs ≡ succ₁ m' ∧ ∞ ≡ succ₁ n' ∧ R m' n')
  {-# ATP prove h #-}
