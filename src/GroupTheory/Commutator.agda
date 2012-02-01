------------------------------------------------------------------------------
-- The commutator operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Commutator where

open import GroupTheory.Base

------------------------------------------------------------------------------

-- The commutator operation.
-- We choose a non-standard symbol, because [_,_] is used by Common.Data.Sum.
⟦_,_⟧ : G → G → G
⟦ a , b ⟧ = a ⁻¹ · b ⁻¹ · a · b
{-# ATP definition ⟦_,_⟧ #-}

⟦⟧-assoc : G → G → G → Set
⟦⟧-assoc a b c = ⟦ ⟦ a , b ⟧ , c ⟧ ≡ ⟦ a , ⟦ b , c ⟧ ⟧
{-# ATP definition ⟦⟧-assoc #-}
