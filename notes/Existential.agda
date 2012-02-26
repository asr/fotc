-- Tested with the development version of Agda on 26 February 2012.

module Existential where

infixr 7 _,_

postulate
  D   : Set
  P Q : D → Set
  P→Q : ∀ {x} → P x → Q x

data ∃ (P : D → Set) : Set where
  _,_ : (x : D) → P x → ∃ P

∃-elim : {P : D → Set}{Q : Set} → ∃ P → (∀ x → P x → Q) → Q
∃-elim (x , p) h = h x p

-- A proof using the existential elimination.
prf₁ : ∃ P → ∃ Q
prf₁ h = ∃-elim h (λ x Px → x , P→Q Px)

-- A proof using the existential elimination with a helper function.
prf₂ : ∃ P → ∃ Q
prf₂ h = ∃-elim h helper
  where
  helper : ∀ x → P x → ∃ Q
  helper x Px = x , P→Q Px

-- A proof using pattern matching.
prf₃ : ∃ P → ∃ Q
prf₃ (x , Px) = x , P→Q Px
