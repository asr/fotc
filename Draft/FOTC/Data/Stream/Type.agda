------------------------------------------------------------------------------
-- The FOTC stream type
------------------------------------------------------------------------------

module Draft.FOTC.Data.Stream.Type where

open import FOTC.Base

------------------------------------------------------------------------------

-- Functor for the FOTC Stream type.
-- StreamF : (D → Set) → D → Set
-- StreamF X ds = ∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ X es

postulate
  Stream : D → Set

  -- Stream is post-fixed point of StreamF.
  Stream-gfp₁ : ∀ ds → Stream ds → ∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ Stream es

  -- Stream is the greatest post-fixed of StreamF.
  Stream-gfp₂ : ∀ ds (P : D → Set) →
                -- P is post-fixed point of StreamF.
                ((∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ P es) → P ds) →
                -- Stream is greater than P.
                P ds → Stream ds
