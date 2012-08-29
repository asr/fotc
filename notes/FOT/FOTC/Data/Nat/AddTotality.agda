------------------------------------------------------------------------------
-- Totality of natural numbers addition
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.AddTotality where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------
-- Interactive proof using the induction principle for natural numbers.
+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = N-ind A A0 ih Nm
  where
    A : D → Set
    A i = N (i + n)

    A0 : A zero
    A0 = subst N (sym (+-0x n)) Nn

    ih : ∀ {i} → A i → A (succ₁ i)
    ih {i} ih = subst N (sym (+-Sx i n)) (sN ih)

-- Combined proof using an instance of the induction principle.
N-ind-instance : ∀ n →
                N (zero + n) →
                (∀ {m} → N (m + n) → N (succ₁ m + n)) →
                ∀ {m} → N m → N (m + n)
N-ind-instance n = N-ind (λ i → N (i + n))

postulate
  +-N₁ : ∀ {m n} → N m → N n → N (m + n)
{-# ATP prove +-N₁ N-ind-instance #-}

-- Combined proof using the induction principle.

-- The translation is
-- ∀ p. app₁(p,zero) →
--      (∀ x. app₁(n,x) → app₁(p,x) → app₁(p,appFn(succ,x))) →   -- indN
--      (∀ x. app₁(n,x) → app₁(p,x))
----------------------------------------------------------------
-- ∀ x y. app₁(n,x) → app₁(n,y) → app₁(n,appFn(appFn(+,x),y))    -- +-N₂

postulate +-N₂ : ∀ {m n} → N m → N n → N (m + n)
-- The ATPs could not prove this postulate.
-- {-# ATP prove +-N₂ N-ind #-}
