------------------------------------------------------------------------------
-- Alter: An unguarded co-recursive function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombinedFOT.FOTC.UnguardedCorecursion.Alter.Alter where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Bool
open import Combined.FOTC.Data.List

------------------------------------------------------------------------------

postulate
  alter    : D
  alter-eq : alter ≡ true ∷ false ∷ alter
{-# ATP axiom alter-eq #-}

postulate
  not₀    : D
  not₀-eq : ∀ b → not₀ · b ≡ not b
{-# ATP axiom not₀-eq #-}

postulate
  alter' : D
  alter'-eq : alter' ≡ true ∷ map not₀ alter'
{-# ATP axiom alter'-eq #-}
