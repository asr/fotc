------------------------------------------------------------------------------
-- A simple network using the Agda standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From (Sander, 1992, pp. 68-69).

module FOT.FOTC.Program.ABP.SimpleNetwork-SL where

open import Data.Bool
open import Data.Stream

------------------------------------------------------------------------------

postulate
  f₁ : {A : Set} → Stream A → Stream A → Stream A
  f₂ : {A : Set} → Stream A → Stream A

{-# NO_TERMINATION_CHECK #-}
trans : {A : Set} → Stream A → Stream A
trans {A} is = os
  where
  ys os : Stream A
  ys = f₁ os is
  os = f₂ ys


Ty : Set → Set
Ty A = (Stream A → Stream A → Stream A) → (Stream A → Stream A) →
       Stream A → Stream A

{-# NO_TERMINATION_CHECK #-}
trans' hys : {A : Set} → Ty A
trans' f₁ f₂ is = f₂ (hys f₁ f₂ is)
hys   f₁ f₂ is = f₁ (trans' f₁ f₂ is) is


------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
