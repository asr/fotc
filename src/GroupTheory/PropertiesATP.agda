------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.PropertiesATP where

open import GroupTheory.Base

------------------------------------------------------------------------------

postulate y≡x⁻¹[xy] : ∀ a b → b ≡ a ⁻¹ · (a · b)
{-# ATP prove y≡x⁻¹[xy] #-}

postulate x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
{-# ATP prove x≡[xy]y⁻¹ #-}

postulate
  rightIdentityUnique : ∀ r → (∀ a → a · r ≡ a) → r ≡ ε
{-# ATP prove rightIdentityUnique #-}

-- A more appropiate version to be used in the proofs.
postulate rightIdentityUnique' : ∀ a r → a · r ≡ a → r ≡ ε
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightIdentityUnique' #-}

postulate
  leftIdentityUnique : ∀ l → (∀ a → l · a ≡ a) → l ≡ ε
{-# ATP prove leftIdentityUnique #-}

-- A more appropiate version to be used in the proofs.
postulate leftIdentityUnique' : ∀ a l → l · a ≡ a → l ≡ ε
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftIdentityUnique' #-}

postulate rightCancellation : ∀ {a b c} → b · a ≡ c · a → b ≡ c
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightCancellation #-}

postulate leftCancellation : ∀ {a b c} → a · b ≡ a · c → b ≡ c
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftCancellation #-}

postulate
  rightInverseUnique : ∀ {a} → ∃[ r ] (a · r ≡ ε) ∧
                                      (∀ r' → a · r' ≡ ε → r ≡ r')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightInverseUnique #-}

-- A more appropiate version to be used in the proofs.
postulate rightInverseUnique' : ∀ {a r} → a · r ≡ ε → a ⁻¹ ≡ r
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rightInverseUnique' #-}

postulate
  leftInverseUnique : ∀ {a} → ∃[ l ] (l · a ≡ ε) ∧
                                     (∀ l' → l' · a ≡ ε → l ≡ l')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftInverseUnique #-}

-- A more appropiate version to be used in the proofs.
postulate leftInverseUnique' : ∀ {a l} → l · a ≡ ε → a ⁻¹ ≡ l
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove leftInverseUnique' #-}

postulate ⁻¹-involutive : ∀ a → a ⁻¹ ⁻¹ ≡ a
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove ⁻¹-involutive #-}

postulate identityInverse : ε ⁻¹ ≡ ε
{-# ATP prove identityInverse #-}

postulate inverseDistributive : ∀ a b → (a · b) ⁻¹ ≡ b ⁻¹ · a ⁻¹
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove inverseDistributive #-}

-- The equation xa = b has an unique solution.
postulate
  xa≡b-uniqueSolution : ∀ a b → ∃[ x ] (x · a ≡ b) ∧
                                       (∀ x' → x' · a ≡ b → x ≡ x')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove xa≡b-uniqueSolution #-}

-- The equation ax = b has an unique solution.
postulate
  ax≡b-uniqueSolution : ∀ a b → ∃[ x ] (a · x ≡ b) ∧
                                       (∀ x' → a · x' ≡ b → x ≡ x')
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove ax≡b-uniqueSolution #-}

-- If the square of every element is the identity, the system is commutative.
-- From: TPTP v5.3.0 problem GRP/GRP001-2.p.
postulate x²≡ε→comm : (∀ a → a · a ≡ ε) → ∀ {b c d} → b · c ≡ d → c · b ≡ d
{-# ATP prove x²≡ε→comm #-}
