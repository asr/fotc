-- Tested with FOT and agda2atp on 07 February 2012.

module Draft.PredicateLogic.SchemataATP where

open import PredicateLogic.Constants

postulate
  id₁ : {P₁ : D → Set} → ∀ {x} → P₁ x → P₁ x
{-# ATP prove id₁ #-}

id₂ : {P₁ : D → Set} → ∀ {x} → P₁ x → P₁ x
id₂ {P} {x} = prf
  where
    postulate prf : P x → P x
    {-# ATP prove prf #-}
