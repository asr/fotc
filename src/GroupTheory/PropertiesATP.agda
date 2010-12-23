------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

module GroupTheory.PropertiesATP where

open import GroupTheory.Base

------------------------------------------------------------------------------

postulate
  y≡x⁻¹[xy] : ∀ a b → b ≡ a ⁻¹ · (a · b)
{-# ATP prove y≡x⁻¹[xy] #-}

postulate
  x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
{-# ATP prove x≡[xy]y⁻¹ #-}

postulate
  rightIdentityUnique : ∃D λ u → (∀ x → x · u ≡ x) ∧
                                 (∀ u' → (∀ x → x · u' ≡ x) → u ≡ u')
{-# ATP prove rightIdentityUnique #-}

-- A more appropiate version to be used in the proofs.
postulate
  rightIdentityUnique' : ∀ x u → x · u ≡ x → ε ≡ u
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightIdentityUnique' #-}

postulate
  leftIdentityUnique : ∃D λ u → (∀ x → u · x ≡ x) ∧
                                (∀ u' → (∀ x → u' · x ≡ x) → u ≡ u')
{-# ATP prove leftIdentityUnique #-}

-- A more appropiate version to be used in the proofs.
postulate
  leftIdentityUnique' : ∀ x u → u · x ≡ x → ε ≡ u
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftIdentityUnique' #-}

postulate
  rightCancellation : ∀ {x y z} → y · x ≡ z · x → y ≡ z
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightCancellation #-}

postulate
  leftCancellation : ∀ {x y z} → x · y ≡ x · z → y ≡ z
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftCancellation #-}

x≡y→xz≡yz : ∀ {a b c} → a ≡ b → a · c ≡ b · c
x≡y→xz≡yz refl = refl

x≡y→zx≡zy : ∀ {a b c} → a ≡ b → c · a ≡ c · b
x≡y→zx≡zy refl = refl

postulate
  rightInverseUnique : ∀ {x} → ∃D λ r → (x · r ≡ ε) ∧
                                        (∀ r' → x · r' ≡ ε → r ≡ r')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightInverseUnique #-}

-- A more appropiate version to be used in the proofs.
postulate
  rightInverseUnique' : ∀ {x r} → x · r ≡ ε → x ⁻¹ ≡ r
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightInverseUnique' #-}

postulate
  leftInverseUnique : ∀ {x} → ∃D λ l → (l · x ≡ ε) ∧
                                       (∀ l' → l' · x ≡ ε → l ≡ l')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftInverseUnique #-}

-- A more appropiate version to be used in the proofs.
postulate
  leftInverseUnique' : ∀ {x l} → l · x ≡ ε → x ⁻¹ ≡ l
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftInverseUnique' #-}

postulate
  ⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≡ x
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove ⁻¹-involutive #-}

postulate
  identityInverse : ε ⁻¹ ≡ ε
{-# ATP prove identityInverse #-}

postulate
  inverseDistributive : ∀ x y → (x · y) ⁻¹ ≡ y ⁻¹ · x ⁻¹
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove inverseDistributive #-}

-- The equation xa = b has an unique solution.
postulate
  xa≡b-uniqueSolution : ∀ a b → ∃D λ x → (x · a ≡ b) ∧
                                         (∀ x' → x' · a ≡ b → x ≡ x')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove xa≡b-uniqueSolution #-}

-- The equation ax = b has an unique solution.
postulate
  ax≡b-uniqueSolution : ∀ a b → ∃D λ x → (a · x ≡ b) ∧
                                         (∀ x' → a · x' ≡ b → x ≡ x')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove ax≡b-uniqueSolution #-}

-- If the square of every element is the identity, the system is commutative.
-- From: TPTP (v5.0.0). File: Problems/GRP/GRP001-2.p
postulate
  x²≡ε→comm : (∀ a → a · a ≡ ε) → ∀ {b c d} → b · c ≡ d → c · b ≡ d
{-# ATP prove x²≡ε→comm #-}
