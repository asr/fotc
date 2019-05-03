------------------------------------------------------------------------------
-- Alter: An unguarded co-recursive function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}
{-# OPTIONS --without-K   #-}

module FOT.FOTC.UnguardedCorecursion.Alter.AlterSL where

open import Codata.Musical.Notation
open import Codata.Musical.Stream
open import Data.Bool.Base

------------------------------------------------------------------------------

-- TODO (2019-01-04): Agda doesn't accept this definition which was
-- accepted by a previous version.
{-# TERMINATING #-}
alter : Stream Bool
alter = true ∷ ♯ (false ∷ ♯ alter)

{-# TERMINATING #-}
alter' : Stream Bool
alter' = true ∷ ♯ (map not alter')
