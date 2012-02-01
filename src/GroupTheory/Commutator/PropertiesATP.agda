------------------------------------------------------------------------------
-- Properties related with the commutator operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Commutator.PropertiesATP where

open import GroupTheory.Base
open import GroupTheory.Commutator

------------------------------------------------------------------------------

postulate ⟦x,y⟧⟦y,x⟧≡ε : ∀ a b → ⟦ a , b ⟧ · ⟦ b , a ⟧ ≡ ε
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove ⟦x,y⟧⟦y,x⟧≡ε #-}

-- If the commutator operation is associative, then commutator of any two
-- elements lies in the center of the group, i.e. a ⟦b,c⟧ = ⟦b,c⟧ a.
-- From: TPTP v5.3.0. File: Problems/GRP/GRP024-5.p
postulate
  ⟦⟧-assoc→⟦⟧-center : (∀ a b c → ⟦⟧-assoc a b c) →
                       (∀ a b c → a · ⟦ b , c ⟧ ≡ ⟦ b , c ⟧ · a)
-- E 1.2: CPU time limit exceeded (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove ⟦⟧-assoc→⟦⟧-center #-}
