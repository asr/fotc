------------------------------------------------------------------------------
-- iter0
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Iter0 where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.Nat

------------------------------------------------------------------------------

postulate
  iter₀    : D → D → D
  iter₀-eq : ∀ f x → iter₀ f x ≡
                     if (iszero₁ x) then [] else x ∷ iter₀ f (f · x)
{-# ATP axiom iter₀-eq #-}

postulate
  powerF    : D → D → D → D
  powerF-0x : ∀ f d →   powerF f zero      d ≡ d
  powerF-Sx : ∀ f n d → powerF f (succ₁ n) d ≡ f · powerF f n d
{-# ATP axiom powerF-0x powerF-Sx #-}

thm : ∀ f x → (∃[ n ] N n ∧ powerF f n x ≡ zero) → List (iter₀ f x)
thm f x (.zero , zN , x₃) = prf
  where postulate prf : List (iter₀ f x)
--        {-# ATP prove prf #-}
thm f x (.(succ₁ n) , sN {n} x₂ , x₃) = prf
  where postulate prf : List (iter₀ f x)
--        {-# ATP prove prf #-}
