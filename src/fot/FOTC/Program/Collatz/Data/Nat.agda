------------------------------------------------------------------------------
-- Natural numbers (added for the Collatz function example)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We don't want populate the FOTC library with more first-order logic
-- axioms.

module FOTC.Program.Collatz.Data.Nat where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

infixr 12 _^_
infixl 10 _/_

------------------------------------------------------------------------------

postulate
  _/_   : D → D → D
  /-x<y : ∀ {m n} → m < n → m / n ≡ zero
  /-x≥y : ∀ {m n} → m ≥ n → m / n ≡ succ₁ ((m ∸ n) / n)
{-# ATP axiom /-x<y /-x≥y #-}

postulate
  _^_ : D → D → D
  ^-0 : ∀ n → n ^ zero      ≡ one
  ^-S : ∀ m n → m ^ succ₁ n ≡ m * m ^ n
{-# ATP axiom ^-0 ^-S #-}

postulate
  even : D → D
  odd  : D → D

  even-0 : even zero            ≡ true
  even-S : ∀ d → even (succ₁ d) ≡ odd d

  odd-0 : odd zero            ≡ false
  odd-S : ∀ d → odd (succ₁ d) ≡ even d
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
