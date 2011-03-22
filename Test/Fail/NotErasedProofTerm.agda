------------------------------------------------------------------------------
-- We do not erase of the proofs terms in the translation
------------------------------------------------------------------------------

module Test.Fail.NotErasedProofTerm where

-- Error message:
-- agda2atp: It is necessary to erase a proof term, but we do know how do it. The internal representation of term to be erased is:
-- Pi r(El (Type (Lit (LitLevel  0))) (Def Test.Fail.NotErasedProofTerm.D [])) (Abs "k" El (Type (Lit (LitLevel  0))) (Def Test.Fail.NotErasedProofTerm._≤_ [r(Var 0 []),r(Var 0 [])]))

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
