------------------------------------------------------------------------------
-- Abelian group base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module GroupTheory.AbelianGroup.Base where

-- We use the group theory base
open import GroupTheory.Base public

------------------------------------------------------------------------------
-- Abelian group theory axioms

-- We only need to add the commutativity axiom.
postulate comm : ∀ a b → a · b ≡ b · a
{-# ATP axiom comm #-}
