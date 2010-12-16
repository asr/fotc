------------------------------------------------------------------------------
-- Properties related with the commutator operation
------------------------------------------------------------------------------

module GroupTheory.Commutator.PropertiesATP where

open import GroupTheory.Base

open import GroupTheory.Commutator using ( ⟦_,_⟧ ; ⟦⟧-assoc )

------------------------------------------------------------------------------

postulate
  ⟦x,y⟧⟦y,x⟧≡ε : ∀ a b → ⟦ a , b ⟧ · ⟦ b , a ⟧ ≡ ε
{-# ATP prove ⟦x,y⟧⟦y,x⟧≡ε #-}

-- If the commutator operation is associative, then commutator of any two
-- elements lies in the center of the group, i.e. x ⟦y,z⟧ = ⟦y,z⟧ x.
-- From: TPTP (v5.0.0). File: Problems/GRP/GRP024-5.p
postulate
  ⟦⟧-assoc→⟦⟧-center : (∀ x y z → ⟦⟧-assoc x y z) →
                       (∀ x y z → x · ⟦ y , z ⟧ ≡ ⟦ y , z ⟧ · x)
{-# ATP prove ⟦⟧-assoc→⟦⟧-center #-}
