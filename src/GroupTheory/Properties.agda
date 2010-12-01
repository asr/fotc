------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

module GroupTheory.Properties where

open import GroupTheory.Base

------------------------------------------------------------------------------

postulate
  rightIdentityUnique : (x r : G) → x ∙ r ≡ x → r ≡ ε
{-# ATP prove rightIdentityUnique #-}

postulate
  leftIdentityUnique : (x l : G) → l ∙ x ≡ x → l ≡ ε
{-# ATP prove leftIdentityUnique #-}

postulate
  leftInverseUnique : (x y : G) → x ∙ y ≡ ε → x ≡ y ⁻¹
{-# ATP prove leftInverseUnique #-}

postulate
  rightInverseUnique : (x y : G) → x ∙ y ≡ ε → y ≡ x ⁻¹
{-# ATP prove rightInverseUnique #-}

postulate
  leftCancellation : (x y z : G) → x ∙ y ≡ x ∙ z → y ≡ z
{-# ATP prove leftCancellation #-}

postulate
  rightCancellation : (x y z : G) → y ∙ x ≡ z ∙ x → y ≡ z
{-# ATP prove rightCancellation #-}

postulate
  ⁻¹-involutive : (x : G)  → x ⁻¹ ⁻¹ ≡ x
{-# ATP prove ⁻¹-involutive #-}

postulate
  identityInverse : ε ⁻¹ ≡ ε
{-# ATP prove identityInverse #-}

postulate
  inverseDistribution : (x y : G) → (x ∙ y) ⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
{-# ATP prove inverseDistribution #-}
