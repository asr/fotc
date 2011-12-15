------------------------------------------------------------------------
-- The unit type
------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.Data.Unit where

------------------------------------------------------------------------
-- The unit type.
-- N.B. The name of this type is "\top", not T.
data ⊤ : Set where
  tt : ⊤
