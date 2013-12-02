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
Stream-pre-fixed {xs} h = Stream-coind (λ ys → ys ≡ ys) h' refl
  where
  postulate h' : xs ≡ xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ xs' ≡ xs'
  {-# ATP prove h' #-}

postulate tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove tailS #-}

streamLength : ∀ {xs} → Stream xs → length xs ≈N ∞
streamLength {xs} Sxs = ≈N-coind (λ m _ → m ≡ m)  h refl
  where
  postulate
    h : length xs ≡ length xs → length xs ≡ zero ∧ ∞ ≡ zero
          ∨ (∃[ m ] ∃[ n ] length xs ≡ succ₁ m ∧ ∞ ≡ succ₁ n ∧ m ≡ m)
  {-# ATP prove h #-}
