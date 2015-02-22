------------------------------------------------------------------------------
-- Natural numbers (added for the Collatz function example)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- We don't want populate the FOTC library with more first-order logic
-- axioms.

module FOTC.Program.Collatz.Data.Nat where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

infixr 8 _^_

------------------------------------------------------------------------------

postulate
  div     : D → D → D
  div-x<y : ∀ {m n} → n ≢ 0' → m < n → div m n ≡ zero
  div-x≥y : ∀ {m n} → n ≢ 0' → m ≥ n → div m n ≡ succ₁ (div (m ∸ n) n)
{-# ATP axiom div-x<y div-x≥y #-}

postulate
  _^_ : D → D → D
  ^-0 : ∀ n → n ^ zero      ≡ 1'
  ^-S : ∀ m n → m ^ succ₁ n ≡ m * m ^ n
{-# ATP axiom ^-0 ^-S #-}

postulate
  even : D → D
  odd  : D → D

  even-0 : even zero            ≡ true
  even-S : ∀ n → even (succ₁ n) ≡ odd n

  odd-0 : odd zero            ≡ false
  odd-S : ∀ n → odd (succ₁ n) ≡ even n
{-# ATP axiom even-0 even-S odd-0 odd-S #-}

Even : D → Set
Even n = even n ≡ true
{-# ATP definition Even #-}

NotEven : D → Set
NotEven n = even n ≡ false
{-# ATP definition NotEven #-}

Odd : D → Set
Odd n = odd n ≡ true
{-# ATP definition Odd #-}
