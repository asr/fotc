------------------------------------------------------------------------------
-- Totality of natural numbers addition
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --schematic-propositional-functions #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.AddTotality where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

module InductionPrinciple where
  -- Interactive proof using the induction principle for natural numbers.
  +-N : ∀ {m n} → N m → N n → N (m + n)
  +-N {m} {n} Nm Nn = N-ind A A0 is Nm
    where
    A : D → Set
    A i = N (i + n)

    A0 : A zero
    A0 = subst N (sym (+-0x n)) Nn

    is : ∀ {i} → A i → A (succ₁ i)
    is {i} ih = subst N (sym (+-Sx i n)) (nsucc ih)

  -- Combined proof using the induction principle.
  --
  -- The translation is
  -- ∀ p. app₁(p,zero) →
  --      (∀ x. app₁(n,x) → app₁(p,x) → app₁(p,appFn(succ,x))) →   -- N-ind
  --      (∀ x. app₁(n,x) → app₁(p,x))
  ----------------------------------------------------------------
  -- ∀ x y. app₁(n,x) → app₁(n,y) → app₁(n,appFn(appFn(+,x),y))    -- +-N

  -- Because the ATPs don't handle induction, them cannot prove this
  -- postulate.
  postulate +-N' : ∀ {m n} → N m → N n → N (m + n)
  -- {-# ATP prove +-N' N-ind #-}

module Instance where
  -- Interactive proof using an instance of the induction principle.
  +-N-ind : ∀ {n} →
            N (zero + n) →
            (∀ {m} → N (m + n) → N (succ₁ m + n)) →
            ∀ {m} → N m → N (m + n)
  +-N-ind {n} = N-ind (λ i → N (i + n))

  +-N : ∀ {m n} → N m → N n → N (m + n)
  +-N {n = n} Nm Nn = +-N-ind A0 is Nm
    where
    A0 : N (zero + n)
    A0 = subst N (sym (+-0x n)) Nn

    is : ∀ {m} → N (m + n) → N (succ₁ m + n)
    is {m} ih = subst N (sym (+-Sx m n)) (nsucc ih)

  -- Combined proof using an instance of the induction principle.
  postulate +-N' : ∀ {m n} → N m → N n → N (m + n)
  {-# ATP prove +-N' +-N-ind #-}
