------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition11 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

data ∃ (A : D → Set) : Set where
  _,_ : (witness : D) → A witness → ∃ A

-- We test the translation of a definition which Agda eta-reduces.
foo : ∀ {n} → N n → D
foo {n} Nn = n
  where
  P : D → Set
  P d = ∃ λ e → d ≡ e
  {-# ATP definition P #-}

  postulate bar : ∀ {d} → P d → ∃ λ e → e ≡ d
  {-# ATP prove bar #-}
