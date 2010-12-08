------------------------------------------------------------------------------
-- Abelian group theory base
------------------------------------------------------------------------------

module AbelianGroupTheory.Base where

-- We use the group theory base
-- N.B. The following module is exported by this module.
open import GroupTheory.Base public

------------------------------------------------------------------------------
-- Abelian group theory axioms

-- We only need to add the commutativity axiom.
postulate
  comm : ∀ x y → x ∙ y ≡ y ∙ x
{-# ATP axiom comm #-}
