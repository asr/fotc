------------------------------------------------------------------------------
-- Lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Nat.List where

open import Interactive.FOTC.Base

-- The FOTC lists of natural numbers type (inductive predicate for
-- total lists of natural numbers).
open import Interactive.FOTC.Data.Nat.List.Type public
