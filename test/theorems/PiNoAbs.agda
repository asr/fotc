------------------------------------------------------------------------------
-- Testing the translation of internal types @Pi _ (NoAbs _ _)@
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}


-- After the patch
--
-- Wed Sep 21 04:50:43 COT 2011  ulfn@chalmers.se
--   * got rid of the Fun constructor in internal syntax (using Pi _ (NoAbs _ _) instead)
--
-- Agda is using @Pi _ (NoAbs _ _)@ for the non-dependent
-- functions. We test some translations of non-dependent functions.

module PiNoAbs where

postulate
  _↔_ : Set → Set → Set
  D   : Set
  A   : Set

postulate foo₁ : ((x : D) → A) → A
{-# ATP prove foo₁ #-}

postulate foo₂ : A → ((x : D) → A)
{-# ATP prove foo₂ #-}

postulate foo₃ : ((x : D) → A) ↔ A
{-# ATP prove foo₃ #-}
