module GroupTheory where

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- We add 3 to the fixities of the standard library.
infix  11 _⁻¹
infixl 10 _∙_

------------------------------------------------------------------------------
-- Group theory axioms

postulate
  G   : Set        -- The group universe.
  ε   : G          -- The identity element.
  _∙_ : G → G → G  -- The group binary operation.
  _⁻¹ : G → G      -- The inverse function.

  associativity : (x y z : G) → x ∙ y ∙ z    ≡ x ∙ (y ∙ z)
  leftIdentity  : (x : G)     →     ε ∙ x    ≡ x
  rightIdentity : (x : G)     →     x ∙ ε    ≡ x
  leftInverse   : (x : G)     →  x ⁻¹ ∙ x    ≡ ε
  rightInverse  : (x : G)     →  x    ∙ x ⁻¹ ≡ ε

-- Properties

rightIdentityUnique : Σ G λ u → (∀ x → x ∙ u ≡ x) ×
                                (∀ u' → (∀ x → x ∙ u' ≡ x) → u ≡ u')
-- Via Agsy {-m}
rightIdentityUnique = ε ,
                      rightIdentity ,
                      λ x x' → begin
                                 ε     ≡⟨ sym (x' ε) ⟩
                                 ε ∙ x ≡⟨ leftIdentity x ⟩
                                 x
                               ∎

leftIdentityUnique : Σ G λ u → (∀ x → u ∙ x ≡ x) ×
                               (∀ u' → (∀ x → u' ∙ x ≡ x) → u ≡ u')
-- Via Agsy {-m}
leftIdentityUnique = ε ,
                     leftIdentity ,
                     λ x x' → begin
                                ε     ≡⟨ sym (x' ε) ⟩
                                x ∙ ε ≡⟨ rightIdentity x ⟩
                                x
                              ∎

rightCancellation : (x y z : G) → y ∙ x ≡ z ∙ x → y ≡ z
rightCancellation x y z = λ hyp → {!-t 20 -m!} -- Agsy fails

leftCancellation : (x y z : G) → x ∙ y ≡ x ∙ z → y ≡ z
leftCancellation x y z = λ hyp → {!-t 20 -m!}  -- Agsy fails

rightInverseUnique : {x : G} → Σ G λ r → (x ∙ r ≡ ε) ×
                                       (∀ r' → x ∙ r' ≡ ε → r ≡ r')
rightInverseUnique {x} = {!-t 20 -m!}  -- Agsy fails

rightInverseUnique' : {x r : G} → x ∙ r ≡ ε → x ⁻¹ ≡ r
rightInverseUnique' {x} {r} = λ hyp → {!-t 20 -m!}  -- Agsy fails

leftInverseUnique : {x : G} → Σ G λ l → (l ∙ x ≡ ε) ×
                                        (∀ l' → l' ∙ x ≡ ε → l ≡ l')
leftInverseUnique {x} = {!-t 20 -m!}  -- Agsy fails


⁻¹-involutive : (x : G)  → x ⁻¹ ⁻¹ ≡ x
⁻¹-involutive x = {!-t 20 -m!}  -- Agsy fails

inverseDistribution : (x y : G) → (x ∙ y) ⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
inverseDistribution x y = {!-t 20 -m!}  -- Agsy fails
