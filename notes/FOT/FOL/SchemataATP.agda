------------------------------------------------------------------------------
-- Testing the FOT schemata
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT and agda2atp on 11 June 2012.

module FOT.FOL.SchemataATP where

open import FOL.Base

------------------------------------------------------------------------------

postulate
  id₁ : {A₁ : D → Set} → ∀ {x} → A₁ x → A₁ x
{-# ATP prove id₁ #-}

id₂ : {A₁ : D → Set} → ∀ {x} → A₁ x → A₁ x
id₂ {A} {x} = prf
  where
    postulate prf : A x → A x
    {-# ATP prove prf #-}
