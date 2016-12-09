------------------------------------------------------------------------------
-- Exclusive disjunction theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.ExclusiveDisjunction.TheoremsI where

-- The theorems below are valid on intuitionistic logic and with an
-- empty domain.
open import FOL.Base hiding ( D≢∅ ; pem )
open import FOL.ExclusiveDisjunction.Base

------------------------------------------------------------------------------

p⊻q→p→¬q : {P Q : Set} → P ⊻ Q → P → ¬ Q
p⊻q→p→¬q (inj₁ _ , h) p q = h (p , q)
p⊻q→p→¬q (inj₂ _ , h) p q = h (p , q)

p⊻q→q→¬p : {P Q : Set} → P ⊻ Q → Q → ¬ P
p⊻q→q→¬p (inj₁ _ , h) q p = h (p , q)
p⊻q→q→¬p (inj₂ _ , h) q p = h (p , q)

p⊻q→¬p→q : {P Q : Set} → P ⊻ Q → ¬ P → Q
p⊻q→¬p→q (inj₁ p , _) ¬p = ⊥-elim (¬p p)
p⊻q→¬p→q (inj₂ q , _) _  = q

p⊻q→¬q→p : {P Q : Set} → P ⊻ Q → ¬ Q → P
p⊻q→¬q→p (inj₁ p , _) ¬q = p
p⊻q→¬q→p (inj₂ q , _) ¬q = ⊥-elim (¬q q)

{-# NON_TERMINATING #-}
mutual
  ¬[p⊻q]→¬p : {P Q : Set} → ¬ (P ⊻ Q) → ¬ P
  ¬[p⊻q]→¬p h₁ = λ p → h₁ (inj₁ p , λ h₂ → ⊥-elim (¬[p⊻q]→¬q h₁ (∧-proj₂ h₂)))

  ¬[p⊻q]→¬q : {P Q : Set} → ¬ (P ⊻ Q) → ¬ Q
  ¬[p⊻q]→¬q h₁ = λ q → h₁ (inj₂ q , λ h₂ → ⊥-elim (¬[p⊻q]→¬p h₁ (∧-proj₁ h₂)))
