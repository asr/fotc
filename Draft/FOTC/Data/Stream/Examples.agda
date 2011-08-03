------------------------------------------------------------------------------
-- Stream examples
------------------------------------------------------------------------------

module Draft.FOTC.Data.Stream.Examples where

open import FOTC.Base

open import FOTC.Data.Stream.Type

------------------------------------------------------------------------------

-- We cannot use the expected definition of zeros because Agda hangs.
zeros : D
zeros = zero ∷ {!!} -- zeros

P : D → Set
P xs = xs ≡ zeros

zerosS : Stream zeros
zerosS = Stream-gfp₂ P (λ {xs} Pxs → zero , zeros , refl , trans Pxs refl) refl
