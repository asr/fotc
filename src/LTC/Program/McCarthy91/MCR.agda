------------------------------------------------------------------------------
-- Well-founded relation use by the properties of the McCarthy 91 function
------------------------------------------------------------------------------

module LTC.Program.McCarthy91.MCR where

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Unary.Numbers

------------------------------------------------------------------------------
-- The MCR relation.

-- To avoid use the name 'MCR' in the name of the properties related
-- with this relation, we use the infix symbol _«_.
MCR : D → D → Set
MCR m n = LT (hundred-one ∸ m) (hundred-one ∸ n)
{-# ATP definition MCR #-}
