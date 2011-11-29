module ExistentialSyntax where

infixr 4 _,_

postulate
  D : Set
  _≡_ : D → D → Set
  refl : ∀ {d} → d ≡ d
  d : D

-- The existential quantifier type on D.
data ∃ (P : D → Set) : Set where
  _,_ : (d : D) → P d → ∃ P

syntax ∃ (λ x → e)  = ∃[ x ] e

t1 : ∃ λ x → x ≡ x
t1 = d , refl

t2 : ∃[ x ] (x ≡ x)
t2 = d , refl

t3 : ∃ λ x → ∃ λ y → x ≡ y
t3 = d , d , refl

t4 : ∃[ x ] ∃[ y ] x ≡ y
t4 = d , d ,  refl
