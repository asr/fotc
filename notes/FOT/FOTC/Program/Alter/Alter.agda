------------------------------------------------------------------------------
-- Alter: An unguarded co-recursive function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Alter.Alter where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------

postulate
  alter    : D
  alter-eq : alter ≡ true ∷ false ∷ alter
{-# ATP axiom alter-eq #-}
