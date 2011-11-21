module Disjunction where

postulate
  _⊎_   : Set → Set → Set
  inj₁  : {A B : Set} → A → A ⊎ B
  inj₂  : {A B : Set} → B → A ⊎ B
  [_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C

⊎-comm : {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm = [ inj₂ , inj₁ ]
