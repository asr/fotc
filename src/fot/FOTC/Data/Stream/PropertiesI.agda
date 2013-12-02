------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream

-----------------------------------------------------------------------------
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

  h' : A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h' _ with h
  ... | x' , xs' , prf , _ = x' , xs' , prf , refl

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS h with Stream-unf h
... | x' , xs' , prf , Sxs' =
  subst Stream (sym (∧-proj₂ (∷-injective prf))) Sxs'

streamLength : ∀ {xs} → Stream xs → length xs ≈N ∞
streamLength {xs} Sxs = ≈N-coind R h refl
  where
  R : D → D → Set
  R m n = m ≡ m

  h : R (length xs) ∞ → length xs ≡ zero ∧ ∞ ≡ zero
        ∨ (∃[ m' ] ∃[ n' ] length xs ≡ succ₁ m' ∧ ∞ ≡ succ₁ n' ∧ R m' n')
  h _ with Stream-unf Sxs
  ... | x' , xs' , xs≡x'∷xs' , _ = inj₂ ( length xs' , ∞ , prf , ∞-eq , refl)
    where
    prf : length xs ≡ succ₁ (length xs')
    prf = trans (lengthCong xs≡x'∷xs') (length-∷ x' xs')
