------------------------------------------------------------------------------
-- Stream examples
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Examples.FOTC.Data.Stream.Examples where

open import FOTC.Base

open import FOTC.Data.Stream

------------------------------------------------------------------------------

-- We cannot use the expected definition of zeros because Agda hangs.
zeros : D
zeros = zero ∷ {!!} -- zeros

P : D → Set
P xs = xs ≡ zeros

zerosS : Stream zeros
zerosS = Stream-gfp₂ P (λ {xs} Pxs → zero , zeros , refl , trans Pxs refl) refl
