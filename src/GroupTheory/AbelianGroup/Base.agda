------------------------------------------------------------------------------
-- Abelian group base
------------------------------------------------------------------------------

module GroupTheory.AbelianGroup.Base where

-- We use the group theory base
open import GroupTheory.Base public

------------------------------------------------------------------------------
-- Abelian group theory axioms

-- We only need to add the commutativity axiom.
postulate
  comm : ∀ x y → x · y ≡ y · x
{-# ATP axiom comm #-}
