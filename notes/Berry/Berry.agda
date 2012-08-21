{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

------------------------------------------------------------------------------
-- The translation from pattern matching equations to equational
-- axioms requires some care because the pattern matching equations
-- are processed from top to bottom and from left to right.

-- From: Herbert P. Sander. A logic of functional programs with an
-- application to concurrency. PhD thesis, Chalmers University of
-- Technology and University of Gothenburg, Department of Computer
-- Sciences, 1992. pp. 12-13.

------------------------------------------------------------------------------

module Berry.Berry where

infix 7 _≡_

postulate
  D         : Set
  zero loop : D
  succ      : D → D

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- For example, the translation of the Haskell function

-- f ∷ Nat → Nat → Nat → Nat
-- f Zero        (Succ Zero) x           = Succ Zero
-- f (Succ Zero) x           Zero        = Succ (Succ Zero)
-- f x           Zero        (Succ Zero) = Succ (Succ (Succ Zero))

-- to the equational axioms

postulate
  f     : D → D → D → D
  f-eq₁ : ∀ x → f zero        (succ zero) x           ≡ succ zero
  f-eq₂ : ∀ x → f (succ zero) x           zero        ≡ succ (succ zero)
  f-eq₃ : ∀ x → f x           zero        (succ zero) ≡ succ (succ (succ zero))
{-# ATP axiom f-eq₁ f-eq₂ f-eq₃ #-}

-- is not correct, because using the Haskell equations we have
--
-- f loop zero (succ zero) = *** Non-terminating ***
--
-- but using the equational axioms we can proof that
postulate
  bad : f loop zero (succ zero) ≡ succ (succ (succ zero))
{-# ATP prove bad #-}
