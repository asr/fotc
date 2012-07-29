{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 12 July 2012.

module Issue3.OtherModule where

open import Issue3.Module

-- The program agda2atp does not translate the ATP pragmas because
-- they are not defined in the imported module.

{-# ATP axiom p #-}

postulate foo : a ≡ b
{-# ATP prove foo #-}
