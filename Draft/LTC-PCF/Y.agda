------------------------------------------------------------------------------
-- The paradoxical combinator
------------------------------------------------------------------------------

module Draft.LTC-PCF.Y where

-- See Henk Barendregt. The Lambda Calculus. Its Syntax and
-- Semantics. Elsevier, revised edition, 2004. 6th. impression,
-- corollary 6.1.3.

open import LTC-PCF.Base

------------------------------------------------------------------------------

Y : D
Y = lam (λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x)))

-- We define a higher-order Y for convenience in writing.
Y₁ : (D → D) → D
Y₁ f = Y · lam f
