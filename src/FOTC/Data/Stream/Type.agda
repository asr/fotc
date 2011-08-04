------------------------------------------------------------------------------
-- The FOTC stream type
------------------------------------------------------------------------------

module FOTC.Data.Stream.Type where

open import FOTC.Base

------------------------------------------------------------------------------

-- Functor for the FOTC Stream type.
-- StreamF : (D → Set) → D → Set
-- StreamF X ds = ∃ λ e → ∃ λ es → X es ∧ ds ≡ e ∷ es

postulate
  Stream : D → Set

-- Stream is post-fixed point of StreamF (d ≤ f d).
postulate
  Stream-gfp₁ : ∀ {xs} → Stream xs →
                ∃ λ x' → ∃ λ xs' → Stream xs' ∧ xs ≡ x' ∷ xs'
{-# ATP axiom Stream-gfp₁ #-}

-- Stream is the greatest post-fixed of StreamF
--
-- (If ∀ e. e ≤ f e => e ≤ d, then d is the greatest post-fixed point
-- of f).
postulate
  Stream-gfp₂ : (P : D → Set) →
                -- P is post-fixed point of StreamF.
                (∀ {xs} → P xs → ∃ λ x' → ∃ λ xs' → P xs' ∧ xs ≡ x' ∷ xs') →
                -- Stream is greater than P.
                ∀ {xs} → P xs → Stream xs

-- Because a greatest post-fixed point is a fixed point, then the
-- Stream predicate is also a pre-fixed point of the functor StreamF
-- (f d ≤ d).
Stream-gfp₃ : ∀ {xs} →
              (∃ λ x' → ∃ λ xs' → Stream xs' ∧ xs ≡ x' ∷ xs') →
              Stream xs
Stream-gfp₃ h = Stream-gfp₂ P helper h
  where
  P : D → Set
  P ws = ∃ λ w' → ∃ λ ws' → Stream ws' ∧ ws ≡ w' ∷ ws'

  helper : {xs : D} → P xs → ∃ λ x' → ∃ λ xs' → P xs' ∧ xs ≡ x' ∷ xs'
  helper (x' , xs' , Sxs' , xs≡x'∷xs') =
    x' , xs' , (Stream-gfp₁ Sxs') , xs≡x'∷xs'
