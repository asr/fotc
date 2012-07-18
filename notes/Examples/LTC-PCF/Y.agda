------------------------------------------------------------------------------
-- The paradoxical combinator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- See (Barendregt 2004, corollary 6.1.3).
--
-- N.B. This is the fixed-point combinator used by (Dybjer 1985).
--
-- References:
--
-- • Henk Barendregt. The Lambda Calculus. Its Syntax and
--   Semantics. Elsevier, revised edition, 2004. 6th. impression.
--
-- • Peter Dybjer. Program verification in a Logical Theory of
--   Constructions. In Jean-Pierre Jouannaud, editor. Functional
--   Programming Languages and Computer Architecture, volume 201 of
--   LNCS, 1985, pages 334–349. Appears in revised form as Programming
--   Methodology Group Report 26, University of Gothenburg and
--   Chalmers University of Technology, June 1986.

module Examples.LTC-PCF.Y where

open import LTC-PCF.Base hiding ( fix ; fix-eq )

------------------------------------------------------------------------------

Y : D
Y = lam (λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x)))

-- We define a higher-order Y for convenience in writing.
Y₁ : (D → D) → D
Y₁ f = Y · lam f
