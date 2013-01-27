------------------------------------------------------------------------------
-- Stream properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------

postulate
  zeros    : D
  zeros-eq : zeros ≡ zero ∷ zeros

zeros-Stream : Stream zeros
zeros-Stream = Stream-coind A prf refl
  where
  A : D → Set
  A xs = xs ≡ zeros

  prf : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] A xs' ∧ xs ≡ x' ∷ xs'
  prf Axs = zero , zeros , refl , trans Axs zeros-eq
