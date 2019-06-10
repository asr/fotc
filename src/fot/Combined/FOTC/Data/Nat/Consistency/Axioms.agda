------------------------------------------------------------------------------
-- Test the consistency of Combined.FOTC.Data.Nat
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module Combined.FOTC.Data.Nat we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module Combined.FOTC.Data.Nat.Consistency.Axioms where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
