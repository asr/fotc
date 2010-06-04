------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

module Examples.Division.Specification where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.ArithmeticPCF
open import LTC.Relation.InequalitiesPCF

------------------------------------------------------------------------------

-- The division result must be a 'N' and it must be correct.
DIV : D → D → D → Set
DIV i j q = (N q) ∧ (∃D (λ r → N r ∧ LT r j ∧ i ≡ j * q + r))
{-# ATP definition DIV #-}
