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
Stream-pre-fixed : (∀ {xs} → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs') →
                   ∀ {xs} → Stream xs
Stream-pre-fixed h = Stream-coind (λ ys → ys ≡ ys) h' refl
  where
  postulate h' : ∀ {xs} → xs ≡ xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ xs' ≡ xs'
  -- TODO (23 December 2013): The translation failed because we do not
  -- know how erase a term.
  -- {-# ATP prove h' #-}

postulate ∷-Stream : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove ∷-Stream #-}

-- Adapted from (Sander 1992, p. 59).
streamLength : ∀ {xs} → Stream xs → length xs ≈N ∞
streamLength {xs} Sxs = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = ∃[ xs ] Stream xs ∧ m ≡ length xs ∧ n ≡ ∞
  {-# ATP definition R #-}

  postulate
    h₁ : ∀ {m n} → R m n →
         m ≡ zero ∧ n ≡ zero
           ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  {-# ATP prove h₁ #-}

  postulate h₂ : R (length xs) ∞
  {-# ATP prove h₂ #-}

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
