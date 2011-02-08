-- Reported by Ana

module Draft.Bugs.BadErrorMessage1 where

open import LTC.Base
open import LTC.Data.Nat

S∸N2N : ∀ {n} → N n → (∀ m → N m → N (n ∸ m)) → ∀ m → N m → N (succ n ∸ m)
S∸N2N {n} Nn h m = indN P' p0 pS
  where P' : D → Set
        P' x = N (succ n ∸ x)
        postulate p0 : P' zero
                  pS : ∀ {x} → N x → P' x → P' (succ x)
        {-# ATP prove p0 #-}

-- agda2atp reports:

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/AgdaLib/Syntax/DeBruijn.hs:286

-- The internal type of p0 is

--  ∀ (n : D) (Nn : N n) (h : (∀ m → N m → N (n ∸ m))) → ...

-- The agda2atp can erase the proof term Nn, but it cannot erase the
-- proof term h.

-- TODO: To change the error message.
