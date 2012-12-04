------------------------------------------------------------------------------
-- Stream examples
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Stream.Examples where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------

-- We cannot use the expected definition of zeros because Agda hangs.
zeros : D
zeros = zero ∷ {!!} -- zeros

P : D → Set
P xs = xs ≡ zeros

zerosS : Stream zeros
zerosS = Stream-coind P (λ {xs} Axs → zero , zeros , refl , trans Axs refl) refl
