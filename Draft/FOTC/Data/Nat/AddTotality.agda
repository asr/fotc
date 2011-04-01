module Draft.FOTC.Data.Nat.AddTotality where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

-- Interactive proof using the induction principle for natural numbers.
+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = indN P P0 ih Nm
  where
    P : D → Set
    P = λ i → N (i + n)

    P0 : P zero
    P0 = subst N (sym (+-0x n)) Nn

    ih : ∀ {i} → N i → P i → P (succ i)
    ih {i} Ni Pi = subst N (sym (+-Sx i n)) (sN Pi)

-- Combined proof using an instance of the induction principle.
indN-instance : (x : D) →
                N (zero + x) →
                (∀ {n} → N n → N (n + x) → N (succ n + x)) →
                ∀ {n} → N n → N (n + x)
indN-instance x = indN (λ i → N (i + x))

postulate
  +-N₁ : ∀ {m n} → N m → N n → N (m + n)
{-# ATP prove +-N₁ indN-instance #-}

-- Combined proof using the induction principle.
postulate
  +-N₂ : ∀ {m n} → N m → N n → N (m + n)
-- The ATPs could not prove this postulate.
{-# ATP prove +-N₂ indN #-}
