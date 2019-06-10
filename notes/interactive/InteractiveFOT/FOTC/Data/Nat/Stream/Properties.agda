------------------------------------------------------------------------------
-- Properties of streams of total natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Data.Nat.Stream.Properties where

open import InteractiveFOT.FOTC.Data.Nat.Stream.Type

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------

postulate
  zeros    : D
  zeros-eq : zeros ≡ zero ∷ zeros

zeros-StreamN : StreamN zeros
zeros-StreamN = StreamN-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ zeros

  h : ∀ {ns} → A ns → ∃[ n' ] ∃[ ns' ] N n' ∧ A ns' ∧ ns ≡ n' ∷ ns'
  h Ans = zero , zeros , nzero , refl , (trans Ans zeros-eq)
