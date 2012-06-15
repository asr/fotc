------------------------------------------------------------------------------
-- Paradoxical combinator properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- See (Barendregt 2004, corollary 6.1.3).
--
-- • Henk Barendregt. The Lambda Calculus. Its Syntax and
--   Semantics. Elsevier, revised edition, 2004. 6th. impression.

module FOT.LTC-PCF.Y.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOT.LTC-PCF.Y

open import LTC-PCF.Base hiding ( fix ; fix-eq )

------------------------------------------------------------------------------

-- The conversion rule for Y.
Y-eq : ∀ f → Y · f ≡ f · (Y · f)
Y-eq f = Y · f             ≡⟨ beta helper f ⟩
         lamW · lamW       ≡⟨ beta W lamW ⟩
         W lamW            ≡⟨ refl ⟩
         f · (lamW · lamW) ≡⟨ cong (_·_ f) (sym (beta helper f)) ⟩
         f · (Y · f)       ∎
  where
  helper : D → D
  helper = λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x))

  W : D → D
  W = λ x → f · (x · x)

  lamW : D
  lamW = lam W

-- The conversion rule for the higher-order Y₁.
Y₁-eq : (f : D → D) → Y₁ f ≡ f (Y₁ f)
Y₁-eq f = Y₁ f                ≡⟨ refl ⟩
          Y · lam f           ≡⟨ Y-eq (lam f) ⟩
          lam f · (Y · lam f) ≡⟨ cong (_·_ (lam f)) refl ⟩
          lam f · Y₁ f        ≡⟨ beta f (Y₁ f) ⟩
          f (Y₁ f)            ∎
