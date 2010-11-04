------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

module Examples.DivisionPCF.SpecificationPCF where

open import LTC.Minimal

open import LTC-PCF.DataPCF.NatPCF
  using ( _+_ ; _*_
        ; N  -- The LTC natural numbers type.
        )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( LT )

------------------------------------------------------------------------------
-- The division result must be a 'N' and it must be correct.
DIV : D → D → D → Set
DIV i j q = N q ∧ ∃D (λ r → N r ∧ LT r j ∧ i ≡ j * q + r)
{-# ATP definition DIV #-}
