------------------------------------------------------------------------------
-- The commutator operation
------------------------------------------------------------------------------

module GroupTheory.Commutator where

open import GroupTheory.Base

------------------------------------------------------------------------------

-- The commutator operation.
-- We choose a non-standard symbol, because [_,_] is used by Common.Data.Sum.
⟦_,_⟧ : G → G → G
⟦ x , y ⟧ = x ⁻¹ ∙ y ⁻¹ ∙ x ∙ y
{-# ATP definition ⟦_,_⟧ #-}

⟦⟧-assoc : G → G → G → Set
⟦⟧-assoc x y z = ⟦ ⟦ x , y ⟧ , z ⟧ ≡ ⟦ x , ⟦ y , z ⟧ ⟧
{-# ATP definition ⟦⟧-assoc #-}