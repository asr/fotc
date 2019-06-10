------------------------------------------------------------------------------
-- Mutual recursive functions
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombinedFOT.FOTC.Data.Nat.MutualRecursiveFunctions where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate
  even : D → D
  odd  : D → D

  even-0 : even zero            ≡ true
  even-S : ∀ d → even (succ₁ d) ≡ odd d

  odd-0 : odd zero            ≡ false
  odd-S : ∀ d → odd (succ₁ d) ≡ even d
{-# ATP axioms even-0 even-S odd-0 odd-S #-}

postulate even-2 : even 2' ≡ true
{-# ATP prove even-2 #-}

postulate even-3 : even 3' ≡ false
{-# ATP prove even-3 #-}

postulate odd-2 : odd 2' ≡ false
{-# ATP prove odd-2 #-}

postulate odd-3 : odd 3' ≡ true
{-# ATP prove odd-3 #-}
