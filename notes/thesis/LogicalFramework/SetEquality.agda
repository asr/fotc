{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We can use a propositional equality parametrized on Set instead of
-- using two "different" equalities on D and M.

module LogicalFramework.SetEquality where

-- We add 3 to the fixities of the standard library.
infix 7 _≡D_ _≡M_

------------------------------------------------------------------------------
-- Domain universe D
postulate
  D : Set

-- Propositional equality on D.
data _≡D_ (x : D) : D → Set where
  refl : x ≡D x

≡D-thm : ∀ {d e} → d ≡D e → e ≡D d
≡D-thm refl = refl

------------------------------------------------------------------------------
-- Domain universe M

data M : Set where
  zero :     M
  succ : M → M

-- Propositional equality on M.
data _≡M_ (n : M) : M → Set where
  refl : n ≡M n

≡M-thm : ∀ {m n} → m ≡M n → n ≡M m
≡M-thm refl = refl

------------------------------------------------------------------------------
-- Propositional equality on Set.

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

≡-thm₁ : ∀ {d e : D} → d ≡ e → e ≡ d
≡-thm₁ refl = refl

≡-thm₂ : ∀ {m n : M} → m ≡ n → n ≡ m
≡-thm₂ refl = refl
