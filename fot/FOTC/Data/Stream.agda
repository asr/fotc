------------------------------------------------------------------------------
-- Streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream where

open import FOTC.Base

-- The FOTC streams type (co-inductive predicate for total streams).
open import FOTC.Data.Stream.Type public
