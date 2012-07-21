------------------------------------------------------------------------------
-- We do not know how erase a proof term in the translation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module NotErasedProofTerm where

postulate
  D    : Set
  _≡_  : D → D → Set
  _≤_  : D → D → Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

thm : ∀ n → N n → (∀ k → k ≤ k) → n ≡ n
thm n Nn h = prf
  where
  -- The internal type of prf is

  --  ∀ (n : D) (Nn : N n) (h : ∀ k → k ≤ k) → ...

  -- The program agda2atp can erase the proof term Nn, but it cannot
  -- erase the proof term h.

  postulate prf : n ≡ n
  {-# ATP prove prf #-}
