-- Tested with FOTC on 29 November 2011.

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

    ih : ∀ {i} → P i → P (succ₁ i)
    ih {i} Pi = subst N (sym (+-Sx i n)) (sN Pi)

-- Combined proof using an instance of the induction principle.
indN-instance : ∀ x →
                N (zero + x) →
                (∀ {n} → N (n + x) → N (succ₁ n + x)) →
                ∀ {n} → N n → N (n + x)
indN-instance x = indN (λ i → N (i + x))

postulate
  +-N₁ : ∀ {m n} → N m → N n → N (m + n)
{-# ATP prove +-N₁ indN-instance #-}

-- Combined proof using the induction principle.

-- The translation is
-- ∀ p. app₁(p,zero) →
--      (∀ x. app₁(n,x) → app₁(p,x) → app₁(p,appFn(succ,x))) →   -- indN
--      (∀ x. app₁(n,x) → app₁(p,x))
----------------------------------------------------------------
-- ∀ x y. app₁(n,x) → app₁(n,y) → app₁(n,appFn(appFn(+,x),y))    -- +-N₂

postulate
  +-N₂ : ∀ {m n} → N m → N n → N (m + n)
-- The ATPs could not prove this postulate.
-- {-# ATP prove +-N₂ indN #-}
