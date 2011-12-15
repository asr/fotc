------------------------------------------------------------------------------
-- Testing the --no-universe-polymorphism flag
------------------------------------------------------------------------------

-- Tested with Agda 2.3.1 on 15 December 2011.

-- {-# OPTIONS --no-universe-polymorphism #-}

module No-Universe-Polymorphism where

-- The following code fails with the --no-universe-polymorphism flag.

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

data List {a : Level} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
