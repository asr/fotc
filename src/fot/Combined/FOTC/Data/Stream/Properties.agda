------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Stream.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Conat
open import Combined.FOTC.Data.Conat.Equality.Type
open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.Stream

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Stream predicate is also a pre-fixed point of the functional
-- StreamF, i.e.
--
-- StreamF Stream ≤ Stream (see Combined.FOTC.Data.Stream.Type).

-- See Issue https://github.com/asr/apia/issues/81 .
Stream-inA : D → Set
Stream-inA xs = ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs'
{-# ATP definition Stream-inA #-}

Stream-in : ∀ {xs} →
            ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs' →
            Stream xs
Stream-in h = Stream-coind Stream-inA h' h
  where
  postulate h' : ∀ {xs} → Stream-inA xs →
                 ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream-inA xs'
  {-# ATP prove h' #-}

-- See Issue https://github.com/asr/apia/issues/81 .
zeros-StreamA : D → Set
zeros-StreamA xs = xs ≡ zeros
{-# ATP definition zeros-StreamA #-}

zeros-Stream : Stream zeros
zeros-Stream = Stream-coind zeros-StreamA h refl
  where
  postulate h : ∀ {xs} → zeros-StreamA xs →
                ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ zeros-StreamA xs'
  {-# ATP prove h #-}

-- See Issue https://github.com/asr/apia/issues/81 .
ones-StreamA : D → Set
ones-StreamA xs = xs ≡ ones
{-# ATP definition ones-StreamA #-}

ones-Stream : Stream ones
ones-Stream = Stream-coind ones-StreamA h refl
  where
  postulate h : ∀ {xs} → ones-StreamA xs →
                ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ ones-StreamA xs'
  {-# ATP prove h #-}

postulate ∷-Stream : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove ∷-Stream #-}

-- Adapted from (Sander 1992, p. 59).

-- See Issue https://github.com/asr/apia/issues/81 .
streamLengthR : D → D → Set
streamLengthR m n = ∃[ xs ] Stream xs ∧ m ≡ length xs ∧ n ≡ ∞
{-# ATP definition streamLengthR #-}

streamLength : ∀ {xs} → Stream xs → length xs ≈ ∞
streamLength {xs} Sxs = ≈-coind streamLengthR h₁ h₂
  where
  postulate
    h₁ : ∀ {m n} → streamLengthR m n →
         m ≡ zero ∧ n ≡ zero
           ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ streamLengthR m' n')
  {-# ATP prove h₁ #-}

  postulate h₂ : streamLengthR (length xs) ∞
  {-# ATP prove h₂ #-}

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
