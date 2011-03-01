------------------------------------------------------------------------------
-- Well-founded relation use by the properties of the McCarthy 91 function
------------------------------------------------------------------------------

module FOTC.Program.McCarthy91.MCR where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The MCR relation.

MCR-f : D → D
MCR-f d = hundred-one ∸ d
{-# ATP definition MCR-f #-}

-- To avoid use the name 'MCR' in the name of the properties related
-- with this relation, we use the infix symbol _«_.
MCR : D → D → Set
MCR m n = LT (MCR-f m) (MCR-f n)
{-# ATP definition MCR #-}
