------------------------------------------------------------------------------
-- Well-founded relation use by the properties of the McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.MCR where

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Unary.Numbers

------------------------------------------------------------------------------
-- The MCR relation.

_«_ : D → D → D
m « n = (hundred-one ∸ m) < (hundred-one ∸ n)
{-# ATP definition _«_ #-}

MCR : D → D → Set
MCR m n = m « n ≡ true
{-# ATP definition MCR #-}
