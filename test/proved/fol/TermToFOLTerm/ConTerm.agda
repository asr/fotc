------------------------------------------------------------------------------
-- Testing the function FOL.Translation.Terms.termToFOLTerm: Con term
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module TermToFOLTerm.ConTerm where

-- We add 3 to the fixities of the standard library.
infixl 9 _+_
infix  7 _≡_

------------------------------------------------------------------------------

data ℕ : Set where
  zero :     ℕ
  succ : ℕ → ℕ

data _≡_ (m : ℕ) : ℕ → Set where
  refl : m ≡ m

sym : ∀ {x y} → x ≡ y → y ≡ x
sym refl = refl

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

+-Sx : ∀ m n → succ m + n ≡ succ (m + n)
+-Sx m n = refl
{-# ATP hint +-Sx #-}

postulate
  +-rightIdentity : ∀ n → n + zero ≡ n
  x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero     n = sym (+-rightIdentity n)
+-comm (succ m) n = prf (+-comm m n)
  where
  postulate prf : m + n ≡ n + m →
                  succ m + n ≡ n + succ m
  {-# ATP prove prf x+Sy≡S[x+y] #-}
