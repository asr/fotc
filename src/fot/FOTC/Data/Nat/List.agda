------------------------------------------------------------------------------
-- Lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Nat.List where

open import FOTC.Base

-- The FOTC lists of natural numbers type (inductive predicate for
-- total lists of natural numbers).
open import FOTC.Data.Nat.List.Type public
