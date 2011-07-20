------------------------------------------------------------------------------
-- The FOTC stream type
------------------------------------------------------------------------------

module FOTC.Data.Stream.Type where

open import FOTC.Base

------------------------------------------------------------------------------

-- Functor for the FOTC Stream type.
-- StreamF : (D → Set) → D → Set
-- StreamF X ds = ∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ X es

postulate
  Stream : D → Set

-- Stream is post-fixed point of StreamF.
postulate
  Stream-gfp₁ : ∀ {xs} → Stream xs →
                ∃ λ x' → ∃ λ xs' → xs ≡ x' ∷ xs' ∧ Stream xs'
{-# ATP axiom Stream-gfp₁ #-}

-- Stream is the greatest post-fixed of StreamF.
postulate
  Stream-gfp₂ : (P : D → Set) →
                -- P is post-fixed point of StreamF.
                (∀ {xs} → P xs → ∃ λ x' → ∃ λ xs' → xs ≡ x' ∷ xs' ∧ P xs') →
                -- Stream is greater than P.
                ∀ {xs} → P xs → Stream xs

-- Because a greatest post-fixed point is a fixed point, the Stream
-- predicate is also a pre-fixed point of the functor StreamF.
Stream-gfp₃ : ∀ {xs} →
              (∃ λ x' → ∃ λ xs' → xs ≡ x' ∷ xs' ∧ Stream xs') →
              Stream xs
Stream-gfp₃ h = Stream-gfp₂ P helper h
  where
  P : D → Set
  P ws = ∃ λ w' → ∃ λ ws' → ws ≡ w' ∷ ws' ∧ Stream ws'

  helper : {xs : D} → P xs → ∃ (λ x' → ∃ (λ xs' → xs ≡ x' ∷ xs' ∧ P xs'))
  helper (x' , xs' , xs≡x'∷xs' , Sxs') =
    x' , xs' , xs≡x'∷xs' , (Stream-gfp₁ Sxs')
