{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LocalPragmas.OtherModule where

open import LocalPragmas

-- The program agda2atp does not translate the ATP pragmas because
-- they are not defined in the module LocalPragmas.

{-# ATP axiom zN #-}

postulate
  N0 : N zero
{-# ATP prove N0 #-}
