------------------------------------------------------------------------------
-- The group commutator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Commutator where

open import GroupTheory.Base

------------------------------------------------------------------------------
-- The group commutator
--
-- There are two definitions for the group commutator:
--
-- [a,b] = aba⁻¹b⁻¹
-- (Saunders Mac Lane and Garret Birkhoff. Algebra. AMS Chelsea
-- Publishing, 3rd edition, 1999. p. 418).
--
-- [a,b] = a⁻¹b⁻¹ab
-- (A. G. Kurosh. The Theory of Groups, vol. 1. Chelsea Publising
-- Company, 2nd edition, 1960. p. 99).
--
-- We choose a non-standard symbol, because [_,_] is used by
-- Common.Data.Sum.

-- We use Kurosh's definition, because this is the definition used
-- by the TPTP v5.3.0 problem GRP/GRP024-5.p.

⟦_,_⟧ : G → G → G
⟦ a , b ⟧ = a ⁻¹ · b ⁻¹ · a · b
{-# ATP definition ⟦_,_⟧ #-}

⟦⟧-assoc : G → G → G → Set
⟦⟧-assoc a b c = ⟦ ⟦ a , b ⟧ , c ⟧ ≡ ⟦ a , ⟦ b , c ⟧ ⟧
{-# ATP definition ⟦⟧-assoc #-}
