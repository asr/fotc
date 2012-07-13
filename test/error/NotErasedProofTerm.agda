------------------------------------------------------------------------------
-- We do not erase of the proofs terms in the translation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module NotErasedProofTerm where

-- $ agda2atp Test/Fail/FOL/NotErasedProofTerm.agda
-- agda2atp: It is necessary to erase the proof term
-- Pi r(El {getSort = Type (Max []), unEl = Def Test.Fail.FOL.NotErasedProofTerm.D []}) (Abs "k" El {getSort = Type (Max []), unEl = Def Test.Fail.FOL.NotErasedProofTerm._≤_ [r(Var 0 []),r(Var 0 [])]})
-- but we do not know how to do it

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
