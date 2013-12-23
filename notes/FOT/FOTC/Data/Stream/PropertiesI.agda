------------------------------------------------------------------------------
-- Stream properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.PropertiesI using ( Stream-pre-fixed )

------------------------------------------------------------------------------

postulate
  zeros    : D
  zeros-eq : zeros ≡ zero ∷ zeros

zeros-Stream : Stream zeros
zeros-Stream = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ zeros

  h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h Axs = zero , zeros , trans Axs zeros-eq , refl
