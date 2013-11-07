------------------------------------------------------------------------------
-- Alter: An unguarded co-recursive function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.UnguardedCorecursion.Alter.Alter where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.List

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
