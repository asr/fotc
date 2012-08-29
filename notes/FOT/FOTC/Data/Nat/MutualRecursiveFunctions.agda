------------------------------------------------------------------------------
-- Mutual recursive functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 29 August 2012.

module FOT.FOTC.Data.Nat.MutualRecursiveFunctions where

open import FOTC.Base

------------------------------------------------------------------------------

postulate
  even : D → D
  odd  : D → D

  even-0 :       even zero      ≡ true
  even-S : ∀ d → even (succ₁ d) ≡ odd d

  odd-0 :       odd zero      ≡ false
  odd-S : ∀ d → odd (succ₁ d) ≡ even d
{-# ATP axiom even-0 even-S odd-0 odd-S #-}

postulate even-2 : even (succ₁ (succ₁ zero)) ≡ true
{-# ATP prove even-2 #-}

postulate even-3 : even (succ₁ (succ₁ (succ₁ zero))) ≡ false
{-# ATP prove even-3 #-}

postulate odd-2 : odd (succ₁ (succ₁ zero)) ≡ false
{-# ATP prove odd-2 #-}

postulate odd-3 : odd (succ₁ (succ₁ (succ₁ zero))) ≡ true
{-# ATP prove odd-3 #-}
