------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.Specification where

open import LTC.Base

open import LTC-PCF.Data.Nat
  using ( _+_ ; _*_
        ; N  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Inequalities using ( LT )

------------------------------------------------------------------------------
-- The division result must be a 'N' and it must be correct.
DIV : D → D → D → Set
DIV i j q = N q ∧ ∃D λ r → N r ∧ LT r j ∧ i ≡ j * q + r
{-# ATP definition DIV #-}
