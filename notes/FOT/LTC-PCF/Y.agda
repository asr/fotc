------------------------------------------------------------------------------
-- The paradoxical combinator
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- See (Barendregt 2004, corollary 6.1.3).

module FOT.LTC-PCF.Y where

open import LTC-PCF.Base hiding ( fix ; fix-eq )

------------------------------------------------------------------------------
-- This is the fixed-point combinator used by (Dybjer 1985).
Y : D
Y = lam (λ f → lam (λ x → f · (x · x)) · lam (λ x → f · (x · x)))

-- We define a higher-order Y.
Y₁ : (D → D) → D
Y₁ f = Y · lam f

------------------------------------------------------------------------------
-- References
--
-- Barendregt, Henk (2004). The Lambda Calculus. Its Syntax and
-- Semantics. 2nd ed. Vol. 103. Studies in Logic and the Foundations
-- of Mathematics. 6th impression. Elsevier.
--
-- Dybjer, Peter (1985). Program Verification in a Logical Theory of
-- Constructions. In: Functional Programming Languages and Computer
-- Architecture. Ed. by Jouannaud,
-- Jean-Pierre. Vol. 201. LNCS. Appears in revised form as Programming
-- Methodology Group Report 26, University of Gothenburg and Chalmers
-- University of Technology, June 1986. Springer, pp. 334–349 (cit. on
-- p. 26).
