module Draft.PredicateLogic.SchemasATP where

open import PredicateLogic.Constants

postulate
  id₁ : {P₁ : D → Set}{x : D} → P₁ x → P₁ x
{-# ATP prove id₁ #-}

id₂ : {P₁ : D → Set}{x : D} → P₁ x → P₁ x
id₂ {P} {x} = prf
  where
    postulate prf : P x → P x
    {-# ATP prove prf #-}
