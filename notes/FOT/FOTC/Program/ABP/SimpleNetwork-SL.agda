------------------------------------------------------------------------------
-- A simple network using the Agda standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From (Sander, 1992, pp. 68-69).
--
-- References:
--
-- • Sander, Herbert P. (1992). A Logic of Functional Programs with an
--   Application to Concurrency. PhD thesis. Department of Computer
--   Sciences: Chalmers University of Technology and University of
--   Gothenburg.

module FOT.FOTC.Program.ABP.SimpleNetwork-SL where

open import Data.Bool
open import Data.Stream

------------------------------------------------------------------------------

postulate
  A  : Set
  f₁ : Stream A → Stream A → Stream A
  f₂ : Stream A → Stream A
  is : Stream A

{-# NO_TERMINATION_CHECK #-}
ys os : Stream A
os = f₂ ys
ys = f₁ os is

Ty : Set → Set
Ty A = (Stream A → Stream A → Stream A) → (Stream A → Stream A) →
       Stream A → Stream A

{-# NO_TERMINATION_CHECK #-}
trans hys : {A : Set} → Ty A
hys   f₁ f₂ is = f₂ (hys f₁ f₂ is)
trans f₁ f₂ is = f₁ (trans f₁ f₂ is) is
