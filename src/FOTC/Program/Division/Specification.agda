------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

module FOTC.Program.Division.Specification where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- The division is total and the result is correct.
DIV : D → D → D → Set
DIV i j q = N q ∧ ∃ λ r → N r ∧ LT r j ∧ i ≡ j * q + r
{-# ATP definition DIV #-}
