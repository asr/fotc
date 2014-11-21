------------------------------------------------------------------------------
-- Some properties of the function iter₀
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Iter0.PropertiesATP where

open import FOTC.Program.Iter0.Iter0

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------

postulate iter₀-0 : ∀ f → iter₀ f zero ≡ []
{-# ATP prove iter₀-0 #-}
