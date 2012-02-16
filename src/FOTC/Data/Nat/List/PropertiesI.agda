------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.List.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.List

------------------------------------------------------------------------------
-- See the ATP version.
postulate ++-ListN : ∀ {ms ns} → ListN ms → ListN ns → ListN (ms ++ ns)
