-- Reported by Ana

module Draft.Bugs.BadErrorMessage where

open import LTC.Base
open import LTC.Data.Nat

S∸N2N : ∀ {n} → N n → (∀ m → N m → N (n ∸ m)) → ∀ m → N m → N (succ n ∸ m)
S∸N2N {n} Nn h m = indN P' p0 pS
  where P' : D → Set
        P' x = N (succ n ∸ x)
        postulate p0 : P' zero
                  pS : ∀ {x} → N x → P' x → P' (succ x)
        {-# ATP prove p0 Nn #-}

-- Agda reports:

-- An internal error has occurred. Please report this as
-- a bug.  Location of the error:
-- src/full/Agda/Syntax/Translation/ConcreteToAbstract.hs:951

-- The problem is we only accept definitions or data constructors in
-- the local hints, i.e we cannot use Nn.

-- TODO: To change the error message.
