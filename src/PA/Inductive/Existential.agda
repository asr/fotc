------------------------------------------------------------------------------
-- Existential quantifier on the inductive PA universe
------------------------------------------------------------------------------

module PA.Inductive.Existential where

------------------------------------------------------------------------------
-- PA universe
open import PA.Inductive.Base.Core public

-- The existential quantifier type on M.
data ∃ (A : M → Set) : Set where
  _,_ : (x : M) → A x → ∃ A

-- Sugar syntax for the existential quantifier.
syntax ∃ (λ x → e) = ∃[ x ] e

-- The existential elimination.
--
-- ∃-elim : {A : M → Set}{B : Set} → ∃ A → (∀ {x} → A x → B) → B
-- ∃-elim (_ , Ax) h = h Ax
