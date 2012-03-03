-- Tested with FOT on 02 March 2012.

module Draft.PA.Inductive.Witness where

-- Writing a proof by contradiction, we still need the existential
-- witness.

open import PA.Inductive.Base
open import PA.Inductive.Properties

------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems

postulate
  -- The principle of indirect proof (proof by contradiction).
  ¬-elim : ∀ {A} → (¬ A → ⊥) → A

  -- ∃ in terms of ∀ and ¬.
  ¬∃¬→∀ : {A : M → Set} → ¬ (∃[ x ] ¬ A x) → ∀ {x} → A x

------------------------------------------------------------------------------

-- We need to choose a natural number in the direct proof.
proof₁ : ∃[ x ] ¬ (x ≡ succ x)
proof₁ = ∃-intro {x = succ zero} x≠Sx

-- We need to choose a natural number in the indirect proof.
proof₂ : ∃[ x ] ¬ (x ≡ succ x)
proof₂ = ¬-elim (λ h → x≠Sx {succ zero} (¬∃¬→∀ h))
