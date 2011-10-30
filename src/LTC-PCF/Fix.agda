------------------------------------------------------------------------------
-- LTC fixed point operator (via the the paradoxical combinator)
------------------------------------------------------------------------------

module LTC-PCF.Fix where

-- See Henk Barendregt. The Lambda Calculus. Its Syntax and
-- Semantics. Elsevier, revised edition, 2004. 6th. impression,
-- corollary 6.1.3.

open import LTC-PCF.Base

------------------------------------------------------------------------------

fix : D
fix = lam (λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x)))

-- We define a higher-order fix for convenience in writing.
abstract
  fix₁ : (D → D) → D
  fix₁ f = fix · lam f

  fix₁-helper : (f : D → D) → fix₁ f ≡ fix · lam f
  fix₁-helper f = refl
