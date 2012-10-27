------------------------------------------------------------------------------
-- Definition of subtraction using a recursive equation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.SubtractionRecursiveEquation where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infixl 9 _∸_

------------------------------------------------------------------------------

postulate
  _∸_  : D → D → D
  ∸-eq : ∀ m n → m ∸ n ≡
         if (iszero₁ n)
            then m
            else if (iszero₁ m)
                    then zero
                    else pred₁ m ∸ pred₁ n
{-# ATP axiom ∸-eq #-}

postulate
  ∸-x0 : ∀ n → n ∸ zero ≡ n
{-# ATP prove ∸-x0 #-}

postulate
  ∸-0S : ∀ n → zero ∸ succ₁ n ≡ zero
{-# ATP prove ∸-0S #-}

postulate
  ∸-SS : ∀ m n → succ₁ m ∸ succ₁ n ≡ m ∸ n
{-# ATP prove ∸-SS #-}

-- asr@pc:~/fotc/notes/thesis$ agda2atp -i ~/fotc/src/fot/  -i. FOTC/SubtractionRecursiveEquation.agda
-- Proving the conjecture in /tmp/FOTC/SubtractionRecursiveEquation/32-8760-0S.tptp ...
-- E 1.6 Tiger Hill proved the conjecture in /tmp/FOTC/SubtractionRecursiveEquation/32-8760-0S.tptp
-- Proving the conjecture in /tmp/FOTC/SubtractionRecursiveEquation/36-8760-SS.tptp ...
-- E 1.6 Tiger Hill proved the conjecture in /tmp/FOTC/SubtractionRecursiveEquation/36-8760-SS.tptp
-- Proving the conjecture in /tmp/FOTC/SubtractionRecursiveEquation/28-8760-x0.tptp ...
-- E 1.6 Tiger Hill proved the conjecture in /tmp/FOTC/SubtractionRecursiveEquation/28-8760-x0.tptp
