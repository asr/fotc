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
