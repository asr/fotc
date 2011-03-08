------------------------------------------------------------------------------
-- Examples of translation of logical schemas
------------------------------------------------------------------------------

module Logic.SchemasATP where

open import Logic.Constants

------------------------------------------------------------------------------

module NonSchemas where

  postulate
    P Q R : Set

  postulate
    ∧-ident : P ∧ ⊤ → P
  {-# ATP prove ∧-ident #-}

  postulate
    ∨-comm  : P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate
    ∧∨-dist : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}

module Schemas where

  postulate
    ∧-ident : {P : Set} → P ∧ ⊤ → P
  {-# ATP prove ∧-ident #-}

  postulate
    ∨-comm  : {P Q : Set} → P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate
    ∧∨-dist : {P Q R : Set} → P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}
