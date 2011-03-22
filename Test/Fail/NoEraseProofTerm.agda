------------------------------------------------------------------------------
-- We do not erase of the proofs terms in the translation
------------------------------------------------------------------------------

module Test.Fail.NoEraseProofTerm where

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

    -- The agda2atp tool can erase the proof term Nn, but it cannot erase the
    -- proof term h.

    postulate prf : n ≡ n
    {-# ATP prove prf #-}
