------------------------------------------------------------------------------
-- Definition of addition using a recursive equation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.AddRecursiveEquation where

open import Combined.FOTC.Base

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/Nat.agda).
infixl 9 _+_

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
