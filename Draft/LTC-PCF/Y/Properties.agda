------------------------------------------------------------------------------
-- Paradoxical combinator properties
------------------------------------------------------------------------------

module Draft.LTC-PCF.Y.Properties where

-- See Henk Barendregt. The Lambda Calculus. Its Syntax and
-- Semantics. Elsevier, revised edition, 2004. 6th. impression,
-- corollary 6.1.3.

open import LTC-PCF.Base

open import Draft.LTC-PCF.Y

open import LTC-PCF.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- The conversion rule for Y.
Y-c : ∀ f → Y · f ≡ f · (Y · f)
Y-c f =
  begin
    Y · f             ≡⟨ beta helper f ⟩
    lamW · lamW       ≡⟨ beta W lamW ⟩
    W lamW            ≡⟨ refl ⟩
    f · (lamW · lamW) ≡⟨ cong (_·_ f) (sym (beta helper f)) ⟩
    f · (Y · f)
  ∎
  where
  helper : D → D
  helper = λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x))

  W : D → D
  W = λ x → f · (x · x)

  lamW : D
  lamW = lam W

-- The conversion rule for (the higher-order) Y₁.
Y-f : (f : D → D) → Y₁ f ≡ f (Y₁ f)
Y-f f =
  begin
    Y₁ f
      ≡⟨ refl ⟩
    Y · lam f
      ≡⟨ Y-c (lam f) ⟩
    lam f · (Y · lam f)
      ≡⟨ cong (_·_ (lam f)) refl ⟩
    lam f · Y₁ f
      ≡⟨ beta f (Y₁ f) ⟩
    f (Y₁ f)
  ∎
