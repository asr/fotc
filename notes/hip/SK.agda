------------------------------------------------------------------------------
-- Testing a proof done using Hip (Haskell Inductive Prover)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module SK where

-- We add 3 to the fixities of the standard library.
infixl 9 _·_
infix  7 _≡_

postulate
  D   : Set
  K S : D
  _·_ : D → D → D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate
 K-eq : ∀ x y → K · x · y ≡ x
 S-eq : ∀ x y z → S · x · y · z ≡ x · z · (y · z)
{-# ATP axiom K-eq S-eq #-}

id : D → D
id x = x
{-# ATP definition id #-}

-- We don't use extensional equality, because _≡_ is not
-- polymorphic. See (Rosén 2012, p. 24).
postulate thm : ∀ x → S · K · K · x ≡ id x
{-# ATP prove thm #-}

------------------------------------------------------------------------------
-- References
--
-- Rosén, D. (2012). Proving Equational Haskell Properties Using
-- Automated Theorem Provers. MA thesis. University of Gothenburg.
