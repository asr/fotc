------------------------------------------------------------------------------
-- Properties related with the group commutator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Commutator.PropertiesATP where

open import GroupTheory.Base
open import GroupTheory.Commutator

------------------------------------------------------------------------------

-- From: A. G. Kurosh. The Theory of Groups, vol. 1. Chelsea Publising
-- Company, 2nd edition, 1960. p. 99.
postulate commutatorInverse : ∀ a b → [ a , b ] · [ b , a ] ≡ ε
{-# ATP prove commutatorInverse #-}

-- If the commutator is associative, then commutator of any two
-- elements lies in the center of the group, i.e. a ⟦b,c⟧ = ⟦b,c⟧ a.
-- From: TPTP 5.5.0 problem GRP/GRP024-5.p.
postulate commutatorAssocCenter : (∀ a b c → commutatorAssoc a b c) →
                                  (∀ a b c → a · [ b , c ] ≡ [ b , c ] · a)
{-# ATP prove commutatorAssocCenter #-}
