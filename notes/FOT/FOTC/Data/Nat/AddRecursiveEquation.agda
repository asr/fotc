------------------------------------------------------------------------------
-- Definition of addition using a recursive equation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.AddRecursiveEquation where

open import FOTC.Base

------------------------------------------------------------------------------

postulate
  _+_  : D → D → D
  +-eq : ∀ m n → m + n ≡ if (iszero₁ m) then n else succ₁ (pred₁ m + n)
{-# ATP axiom +-eq #-}

postulate
  +-0x : ∀ n →   zero    + n ≡ n
  +-Sx : ∀ m n → succ₁ m + n ≡ succ₁ (m + n)
{-# ATP prove +-0x #-}
{-# ATP prove +-Sx #-}

-- $ agda2atp -i. -i ~/fotc/fot/ FOT/FOTC/Data/Nat/AddRecursiveEquation.agda
-- Proving the conjecture in /tmp/FOT/FOTC/Data/Nat/AddRecursiveEquation/23-43-Sx.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/FOT/FOTC/Data/Nat/AddRecursiveEquation/23-43-Sx.tptp
-- Proving the conjecture in /tmp/FOT/FOTC/Data/Nat/AddRecursiveEquation/22-43-0x.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/FOT/FOTC/Data/Nat/AddRecursiveEquation/22-43-0x.tptp
