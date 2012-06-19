{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Issues.LocalPragmas.OtherModule where

open import Issues.LocalPragmas

-- The program agda2atp does not translate the ATP pragmas because
-- they are not defined in the module Issues.LocalPragmas.

{-# ATP axiom zN #-}

postulate
  N0 : N zero
{-# ATP prove N0 #-}
