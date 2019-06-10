------------------------------------------------------------------------------
-- Some properties of the function iter₀
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Iter0.Properties where

open import Combined.FOTC.Program.Iter0.Iter0

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List

------------------------------------------------------------------------------

postulate iter₀-0 : ∀ f → iter₀ f zero ≡ []
{-# ATP prove iter₀-0 #-}
