------------------------------------------------------------------------------
-- Definition of addition using a recursive equation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.AddRecursiveEquation where

open import FOTC.Base

------------------------------------------------------------------------------

postulate
  _+_  : D → D → D
  +-eq : ∀ m n → m + n ≡ (if (iszero₁ m) then n else succ₁ (pred₁ m + n))
{-# ATP axiom +-eq #-}

postulate
  +-0x : ∀ n → zero + n      ≡ n
  +-Sx : ∀ m n → succ₁ m + n ≡ succ₁ (m + n)
{-# ATP prove +-0x #-}
{-# ATP prove +-Sx #-}

-- $ cd fotc/notes/thesis
-- $ agda -i. -i ~/fot FOTC/AddRecursiveEquation.agda
-- $ apia -i. -i ~/fot FOTC/AddRecursiveEquation.agda
-- Proving the conjecture in /tmp/FOTC/AddRecursiveEquation/21-43-Sx.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
-- Proving the conjecture in /tmp/FOTC/AddRecursiveEquation/20-43-0x.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
