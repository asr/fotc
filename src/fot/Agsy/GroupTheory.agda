------------------------------------------------------------------------------
-- Group theory properties using Agsy
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas     #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Tested with the development version of the Agda standard library on
-- 02 February 2012.

module Agsy.GroupTheory where

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Algebra.agda)
infix  11 _⁻¹
infixl 10 _·_

------------------------------------------------------------------------------
-- Group theory axioms

postulate
  G   : Set        -- The universe.
  ε   : G          -- The identity element.
  _·_ : G → G → G  -- The binary operation.
  _⁻¹ : G → G      -- The inverse function.

  assoc         : ∀ x y z → x · y · z    ≡ x · (y · z)
  leftIdentity  : ∀ x     →     ε · x    ≡ x
  rightIdentity : ∀ x     →     x · ε    ≡ x
  leftInverse   : ∀ x     →  x ⁻¹ · x    ≡ ε
  rightInverse  : ∀ x     →  x    · x ⁻¹ ≡ ε

-- Properties

y≡x⁻¹[xy] : ∀ a b → b ≡ a ⁻¹ · (a · b)
y≡x⁻¹[xy] a b = {!-t 20 -m!}  -- Agsy fails

x≡[xy]y⁻¹ : ∀ a b → a ≡ (a · b) · b ⁻¹
x≡[xy]y⁻¹ a b = {!-t 20 -m!}  -- Agsy fails

rightIdentityUnique : Σ G λ u → (∀ x → x · u ≡ x) ×
                                (∀ u' → (∀ x → x · u' ≡ x) → u ≡ u')
rightIdentityUnique = {!-t 20 -m!}  -- Agsy fails
  -- ε
  -- , rightIdentity
  -- , λ x x' → begin
  --              ε     ≡⟨ sym (x' ε) ⟩
  --              ε · x ≡⟨ leftIdentity x ⟩
  --              x
  --            ∎

rightIdentityUnique' : ∀ x u → x · u ≡ x → ε ≡ u
rightIdentityUnique' x u xu≡x = {!-t 20 -m!}  -- Agsy fails

leftIdentityUnique : Σ G λ u → (∀ x → u · x ≡ x) ×
                               (∀ u' → (∀ x → u' · x ≡ x) → u ≡ u')
leftIdentityUnique = {!-t 20 -m!}  -- Agsy fails
  -- ε
  -- , leftIdentity
  -- , λ x x' → begin
  --              ε     ≡⟨ sym (x' ε) ⟩
  --              x · ε ≡⟨ rightIdentity x ⟩
  --              x
  --            ∎

leftIdentityUnique' : ∀ x u → u · x ≡ x → ε ≡ u
leftIdentityUnique' x u ux≡x = {!-t 20 -m!}

rightCancellation : ∀ x y z → y · x ≡ z · x → y ≡ z
rightCancellation x y z = λ hyp → {!-t 20 -m!} -- Agsy fails

leftCancellation : ∀ x y z → x · y ≡ x · z → y ≡ z
leftCancellation x y z = λ hyp → {!-t 20 -m!}  -- Agsy fails

leftCancellationER : (x y z : G) → x · y ≡ x · z → y ≡ z
leftCancellationER x y z x·y≡x·z =
  begin
    y              ≡⟨ sym (leftIdentity y) ⟩
    ε · y          ≡⟨ subst (λ t → ε · y ≡ t · y) (sym (leftInverse x)) refl ⟩
    x ⁻¹ · x · y   ≡⟨ assoc (x ⁻¹) x y ⟩
    x ⁻¹ · (x · y) ≡⟨ subst (λ t → x ⁻¹ · (x · y) ≡ x ⁻¹ · t) x·y≡x·z refl ⟩
    x ⁻¹ · (x · z) ≡⟨ sym (assoc (x ⁻¹) x z) ⟩
    x ⁻¹ · x · z   ≡⟨ subst (λ t → x ⁻¹ · x · z ≡ t · z) (leftInverse x) refl ⟩
    ε · z          ≡⟨ leftIdentity z ⟩
    z
  ∎

rightInverseUnique : ∀ x → Σ G λ r → (x · r ≡ ε) ×
                                     (∀ r' → x · r' ≡ ε → r ≡ r')
rightInverseUnique x = {!-t 20 -m!}  -- Agsy fails

rightInverseUnique' : ∀ x r → x · r ≡ ε → x ⁻¹ ≡ r
rightInverseUnique' x r = λ hyp → {!-t 20 -m!}  -- Agsy fails

leftInverseUnique : ∀ x → Σ G λ l → (l · x ≡ ε) ×
                                    (∀ l' → l' · x ≡ ε → l ≡ l')
leftInverseUnique x = {!-t 20 -m!}  -- Agsy fails

⁻¹-involutive : ∀ x  → x ⁻¹ ⁻¹ ≡ x
⁻¹-involutive x = {!-t 20 -m!}  -- Agsy fails

inverseDistribution : ∀ x y → (x · y) ⁻¹ ≡ y ⁻¹ · x ⁻¹
inverseDistribution x y = {!-t 20 -m!}  -- Agsy fails

-- If the square of every element is the identity, the system is
-- commutative. From: TPTP 6.1.0. File: Problems/GRP/GRP001-2.p
x²≡ε→comm : (∀ a → a · a ≡ ε) → ∀ {b c d} → b · c ≡ d → c · b ≡ d
x²≡ε→comm hyp {b} {c} {d} bc≡d = {!-t 20 -m!}  -- Agsy fails
