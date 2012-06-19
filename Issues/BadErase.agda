------------------------------------------------------------------------------
-- The translation is badly erasing the universal quantification
------------------------------------------------------------------------------

-- Found on 14 March 2012.

module Issues.BadErase where

postulate
  _↔_ : Set → Set → Set
  D   : Set
  A   : Set

postulate bad₁ : ((x : D) → A) → A
{-# ATP prove bad₁ #-}

postulate bad₂ : A → ((x : D) → A)
{-# ATP prove bad₂ #-}

postulate bad₃ : ((x : D) → A) ↔ A
{-# ATP prove bad₃ #-}
