------------------------------------------------------------------------------
-- Addition as a function constant
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.AddConstant where

open import FOTC.Base

------------------------------------------------------------------------------

postulate
  +    : D
  +-eq : ∀ m n → + · m · n ≡ if (iszero₁ m) then n else succ₁ (+ · (pred₁ m) · n)
{-# ATP axiom +-eq #-}

postulate
  +-0x : ∀ n → + · zero · n ≡ n
  +-Sx : ∀ m n → + · (succ₁ m) · n ≡ succ₁ (+ · m · n)
{-# ATP prove +-0x #-}
{-# ATP prove +-Sx #-}

-- $ cd fotc/notes/thesis
-- $ agda -i. -i ~/fot FOTC/AddConstant.agda
-- $ agda2atp -i. -i ~/fot FOTC/AddConstant.agda
-- Proving the conjecture in /tmp/FOTC/AddConstant/21-43-Sx.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
-- Proving the conjecture in /tmp/FOTC/AddConstant/20-43-0x.tptp ...
-- E 1.7 Jun Chiabari proved the conjecture
