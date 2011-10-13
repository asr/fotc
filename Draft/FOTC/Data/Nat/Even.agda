------------------------------------------------------------------------------
-- Even predicate
------------------------------------------------------------------------------

module Draft.FOTC.Data.Nat.Even where

open import FOTC.Base

data Even : D → Set where
  zeroeven : Even zero
  nexteven : ∀ {d} → Even d → Even (succ (succ d))

indEven : (P : D → Set) →
          P zero →
          (∀ {d} → P d → P (succ (succ d))) →
          ∀ {d} → Even d → P d
indEven P P0 h zeroeven      = P0
indEven P P0 h (nexteven Ed) = h (indEven P P0 h Ed)
