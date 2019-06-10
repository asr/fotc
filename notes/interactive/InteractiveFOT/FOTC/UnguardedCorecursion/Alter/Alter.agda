------------------------------------------------------------------------------
-- Alter: An unguarded co-recursive function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.UnguardedCorecursion.Alter.Alter where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.List

------------------------------------------------------------------------------

postulate
  alter    : D
  alter-eq : alter ≡ true ∷ false ∷ alter

postulate
  not₀    : D
  not₀-eq : ∀ b → not₀ · b ≡ not b

postulate
  alter' : D
  alter'-eq : alter' ≡ true ∷ map not₀ alter'
