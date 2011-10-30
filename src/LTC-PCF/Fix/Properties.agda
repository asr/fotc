------------------------------------------------------------------------------
-- LTC fixed point operator properties
------------------------------------------------------------------------------

module LTC-PCF.Fix.Properties where

-- See Henk Barendregt. The Lambda Calculus. Its Syntax and
-- Semantics. Elsevier, revised edition, 2004. 6th. impression,
-- corollary 6.1.3.

open import LTC-PCF.Base

open import LTC-PCF.Fix

open import LTC-PCF.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- The conversion rule for fix.
private
  fix-c : ∀ f → fix · f ≡ f · (fix · f)
  fix-c f =
    begin
      fix · f           ≡⟨ beta helper f ⟩
      lamW · lamW       ≡⟨ beta W lamW ⟩
      W lamW            ≡⟨ refl ⟩
      f · (lamW · lamW) ≡⟨ cong (_·_ f) (sym (beta helper f)) ⟩
      f · (fix · f)
    ∎
    where
    helper : D → D
    helper = λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x))

    W : D → D
    W = λ x → f · (x · x)

    lamW : D
    lamW = lam W

-- The conversion rule for (the higher-order) fix₁.
-- See the comments to the conversion rules in FOTC.Base.
fix-f : (f : D → D) → fix₁ f ≡ f (fix₁ f)
fix-f f =
  begin
    fix₁ f
      ≡⟨ fix₁-helper f ⟩
    fix · lam f
      ≡⟨ fix-c (lam f) ⟩
    lam f · (fix · lam f)
      ≡⟨ cong (_·_ (lam f)) (sym (fix₁-helper f)) ⟩
    lam f · fix₁ f
      ≡⟨ beta f (fix₁ f) ⟩
    f (fix₁ f)
  ∎
{-# ATP hint fix-f #-}
