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

fnMCR : D → D
fnMCR d = hundred-one ∸ d
{-# ATP definition fnMCR #-}

-- To avoid use the name 'MCR' in the name of the properties related
-- with this relation, we use the infix symbol _«_.
MCR : D → D → Set
MCR m n = LT (fnMCR m) (fnMCR n)
{-# ATP definition MCR #-}
