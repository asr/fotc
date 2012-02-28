-- Tested with the development version of Agda on 27 February 2012.

-- Thm: (∃x)A(x), (∀x)(A(x) ⇒ B(x)) ⊢ (∃x)B(x)

-- From: Elliott Mendelson. Introduction to mathematical logic. Chapman &
-- Hall, 4th edition, 1997, p. 155.

-- Rule A4: (∀x)A(x) ⇒ A(t) (with some conditions)
-- Rule E4: A(t) ⇒ (∃x)A(x) (with some conditions)
-- Rule C: From (∃x)A(x) to A(t) (with some conditions)

-- 1. (∃x)A(x)          Hyp
-- 2. (∀x)(A(x) ⇒ B(x)) Hyp
-- 3. A(b)              1, rule C
-- 4. A(b) ⇒ B(b)       2, rule A4
-- 5. B(b)              4,3 MP
-- 6. (∃x)B(x)          5, rule E4

module Existential where

postulate
  D   : Set
  A B : D → Set

module Witness where

  infixr 7 _,_

  data ∃ (A : D → Set) : Set where
    _,_ : ∀ x → A x → ∃ A

  ∃-elim : {A : D → Set}{B : Set} → ∃ A → (∀ x → A x → B) → B
  ∃-elim (x , Ax) h = h x Ax

  -- A proof using the existential elimination.
  prf₁ : ∃ A → (∀ {x} → A x → B x) → ∃ B
  prf₁ h₁ h₂ = ∃-elim h₁ (λ x Ax → x , (h₂ Ax))

  -- A proof using pattern matching.
  prf₂ : ∃ A → (∀ {x} → A x → B x) → ∃ B
  prf₂ (x , Ax) h = x , h Ax

module NonWitness₁ where

  data ∃ (A : D → Set) : Set where
    ∃-intro : ∀ {x} → A x → ∃ A

  ∃-elim : {A : D → Set}{B : Set} → ∃ A → (∀ {x} → A x → B) → B
  ∃-elim (∃-intro Ax) h = h Ax

  -- A proof using the existential elimination.
  prf₁ : ∃ A → (∀ {x} → A x → B x) → ∃ B
  prf₁ h₁ h₂ = ∃-elim h₁ (λ Ax → ∃-intro (h₂ Ax))

  -- A proof using pattern matching.
  prf₂ : ∃ A → (∀ {x} → A x → B x) → ∃ B
  prf₂ (∃-intro Ax) h = ∃-intro (h Ax)

module NonWitness₂ where

  -- We add 3 to the fixities of the standard library.
  infix 6 ¬_

  -- The empty type.
  data ⊥ : Set where

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  ¬_ : Set → Set
  ¬ A = A → ⊥

  ∃ : (D → Set) → Set
  ∃ A = ¬ (∀ x → ¬ (A x))

  prf : ∃ A → (∀ x → A x → B x) → ∃ B
  prf h₁ h₂ h₃ = h₁ (λ x Ax → h₃ x (h₂ x Ax))
