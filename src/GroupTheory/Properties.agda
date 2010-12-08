------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

module GroupTheory.Properties where

open import GroupTheory.Base

------------------------------------------------------------------------------

postulate
  rightIdentityUnique : ∃D λ u → (∀ x → x ∙ u ≡ x) ∧
                                 (∀ u' → (∀ x → x ∙ u' ≡ x) → u ≡ u')
{-# ATP prove rightIdentityUnique #-}

postulate
  leftIdentityUnique : ∃D λ u → (∀ x → u ∙ x ≡ x) ∧
                                (∀ u' → (∀ x → u' ∙ x ≡ x) → u ≡ u')
{-# ATP prove leftIdentityUnique #-}

postulate
  rightCancellation : ∀ {x y z} → y ∙ x ≡ z ∙ x → y ≡ z
{-# ATP prove rightCancellation #-}

postulate
  leftCancellation : ∀ {x y z} → x ∙ y ≡ x ∙ z → y ≡ z
{-# ATP prove leftCancellation #-}

postulate
  rightInverseUnique : ∀ {x} → ∃D λ r → (x ∙ r ≡ ε) ∧
                                        (∀ r' → x ∙ r' ≡ ε → r ≡ r')
{-# ATP prove rightInverseUnique #-}

-- A more appropiate version to be used in the proofs.
postulate
  rightInverseUnique' : ∀ {x r} → x ∙ r ≡ ε → x ⁻¹ ≡ r
{-# ATP prove rightInverseUnique' #-}

postulate
  leftInverseUnique : ∀ {x} → ∃D λ l → (l ∙ x ≡ ε) ∧
                                       (∀ l' → l' ∙ x ≡ ε → l ≡ l')
{-# ATP prove leftInverseUnique #-}

-- A more appropiate version to be used in the proofs.
postulate
  leftInverseUnique' : ∀ {x l} → l ∙ x ≡ ε → x ⁻¹ ≡ l
{-# ATP prove leftInverseUnique' #-}

postulate
  ⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≡ x
{-# ATP prove ⁻¹-involutive #-}

postulate
  identityInverse : ε ⁻¹ ≡ ε
{-# ATP prove identityInverse #-}

postulate
  inverseDistribution : ∀ x y → (x ∙ y) ⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
{-# ATP prove inverseDistribution #-}

-- The equation xa = b has an unique solution.
postulate
  xa≡b-uniqueSolution : ∀ a b → ∃D λ x → (x ∙ a ≡ b) ∧
                                         (∀ x' → x' ∙ a ≡ b → x ≡ x')
{-# ATP prove xa≡b-uniqueSolution #-}

-- The equation ax = b has an unique solution.
postulate
  ax≡b-uniqueSolution : ∀ a b → ∃D λ x → (a ∙ x ≡ b) ∧
                                         (∀ x' → a ∙ x' ≡ b → x ≡ x')
{-# ATP prove ax≡b-uniqueSolution #-}

-- If the square of every element is the identity, the system is commutative.
-- From: TPTP (v5.0.0). File: Problems/GRP/GRP001-2.
postulate
  xx≡ε→comm : ∀ x a b c → x ∙ x ≡ ε → a ∙ b ≡ c → b ∙ a ≡ c

-- Paper proof:
-- 1. c(ab)  = cc  (Hypothesis ab = c).
-- 2. c(ab)  = ε   (Hypothesis cc = ε).
-- 3. c(ab)b = b   (By 2).
-- 4. ca(bb) = b   (Associativity).
-- 5. ca     = b   (Hypothesis bb = ε).
-- 6. (ca)a  = ba  (By 5).
-- 7. c(aa)  = ba  (Associativity).
-- 6. c      = ba  (Hypothesis aa = ε).

-- E 1.2 no-success due to timeout (300 sec).
-- Equinox 5.0alpha (2010-06-29) no-success due to timeout (300 sec).
-- Metis 2.3 (release 20101019) no-success due to timeout (300 sec).
-- {-# ATP prove xx≡ε→comm #-}
