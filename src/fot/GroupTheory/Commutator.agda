------------------------------------------------------------------------------
-- The group commutator
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module GroupTheory.Commutator where

open import GroupTheory.Base

------------------------------------------------------------------------------
-- The group commutator
--
-- There are two definitions for the group commutator:
--
-- [a,b] = aba⁻¹b⁻¹ (Mac Lane and Garret 1999, p. 418), or
--
-- [a,b] = a⁻¹b⁻¹ab (Kurosh 1960, p. 99).
--
-- We use Kurosh's definition, because this is the definition used by
-- the TPTP 6.4.0 problem GRP/GRP024-5.p. Actually the problem uses
-- the definition
--
-- [a,b] = a⁻¹(b⁻¹(ab)).

[_,_] : G → G → G
[ a , b ] = a ⁻¹ · b ⁻¹ · a · b
{-# ATP definition [_,_] #-}

commutatorAssoc : G → G → G → Set
commutatorAssoc a b c = [ [ a , b ] , c ] ≡ [ a , [ b , c ] ]
{-# ATP definition commutatorAssoc #-}

------------------------------------------------------------------------------
-- References
--
-- Mac Lane, S. and Birkhof, G. (1999). Algebra. 3rd ed. AMS Chelsea
-- Publishing.
--
-- Kurosh, A. G. (1960). The Theory of Groups. 2nd
-- ed. Vol. 1. Translated and edited by K. A. Hirsch. Chelsea
-- Publising Company.
