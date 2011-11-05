------------------------------------------------------------------------------
-- Properties related with the commutator operation
------------------------------------------------------------------------------

module GroupTheory.Commutator.PropertiesATP where

open import GroupTheory.Base
open import GroupTheory.Commutator

------------------------------------------------------------------------------

postulate ⟦x,y⟧⟦y,x⟧≡ε : ∀ a b → ⟦ a , b ⟧ · ⟦ b , a ⟧ ≡ ε
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove ⟦x,y⟧⟦y,x⟧≡ε #-}

-- If the commutator operation is associative, then commutator of any two
-- elements lies in the center of the group, i.e. x ⟦y,z⟧ = ⟦y,z⟧ x.
-- From: TPTP v5.2.0. File: Problems/GRP/GRP024-5.p
postulate
  ⟦⟧-assoc→⟦⟧-center : (∀ x y z → ⟦⟧-assoc x y z) →
                       (∀ x y z → x · ⟦ y , z ⟧ ≡ ⟦ y , z ⟧ · x)
-- E 1.2: CPU time limit exceeded (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove ⟦⟧-assoc→⟦⟧-center #-}
