------------------------------------------------------------------------------
-- From N as the least fixed-point to N using data
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We want to represent the total natural numbers data type
--
-- data N : D → Set where
--   nzero : N zero
--   nsucc : ∀ {n} → N n → N (succ₁ n)
--
-- using the representation of N as the least fixed-point.

module LeastFixedPoints.N where

open import FOTC.Base
open import FOTC.Base.PropertiesI

-- infixl 9 _+_

------------------------------------------------------------------------------
-- Basic definitions

-- Pre-fixed point  : d is a pre-fixed point of f if f d ≤ d

-- Post-fixed point : d is a post-fixed point of f if d ≤ f d

-- Fixed-point      : d is a fixed-point of f if f d = d

-- Least pre-fixed point : d is the least pre-fixed point of f if
-- 1. f d ≤ d  -- d is a pre-fixed point of f
-- 2. ∀ e. f e ≤ e ⇒ d ≤ e

-- Least fixed-point : d is the least fixed-point of f if
-- 1. f d = d  -- d is a fixed-point of f
-- 2. ∀ e. f e ≤ e ⇒ d ≤ e

-- Thm: If d is the least pre-fixed point of f, then d is the least
-- fixed-point of f (Ésik, 2009, p. 31).

-- Thm: If d is the greatest post-fixed point of f, then d is the greatest
-- fixed-point of f (Ésik, 2009, p. 31).

------------------------------------------------------------------------------
-- Auxiliary definitions and properties

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

cong : (f : D → D) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------------
-- N is a least fixed-point of a functor

-- The functor.
NatF : (D → Set) → D → Set
NatF P n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ P n')

-- The natural numbers are the least fixed-point of NatF.
postulate
  N : D → Set

  -- N is a pre-fixed point of NatF.
  --
  -- Peter: It corresponds to the introduction rules.
  N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n

  -- The higher-order version.
  N-in-ho : ∀ {n} → NatF N n → N n

  -- N is the least pre-fixed point of NatF.
  --
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  N-least-pre-fixed :
    ∀ (A : D → Set) {n} →
    (n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
    N n → A n

  -- Higher-order version (incomplete?)
  N-least-pre-fixed-ho :
    ∀ (A : D → Set) {n} →
    (NatF A n → A n) →
    N n → A n

------------------------------------------------------------------------------
-- From/to N-in/N-in-ho.

N-in₁ : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n
N-in₁ = N-in-ho

N-in-ho₁ : ∀ {n} → NatF N n → N n
N-in-ho₁ = N-in₁

------------------------------------------------------------------------------
-- From/to N-least-pre-fixed/N-least-pre-fixed-ho
N-least-pre-fixed' :
  ∀ (A : D → Set) {n} →
  (n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
  N n → A n
N-least-pre-fixed' = N-least-pre-fixed-ho

N-least-pre-fixed-ho' :
  ∀ (A : D → Set) {n} →
  (NatF A n → A n) →
  N n → A n
N-least-pre-fixed-ho' = N-least-pre-fixed

------------------------------------------------------------------------------
-- The data constructors of N.
nzero : N zero
nzero = N-in (inj₁ refl)

nsucc : ∀ {n} → N n → N (succ₁ n)
nsucc Nn = N-in (inj₂ (_ , refl , Nn))

------------------------------------------------------------------------------
-- Because N is the least pre-fixed point of NatF (i.e. N-in and
-- N-ind), we can proof that N is also a post-fixed point of NatF.

-- N is a post-fixed point of NatF.
N-post-fixed : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
N-post-fixed = N-least-pre-fixed A prf
  where
  A : D → Set
  A m = m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')

  prf : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
  prf (inj₁ h)              = inj₁ h
  prf (inj₂ (m' , h , Am')) = inj₂ (m' , h , prf₂ Am')
    where
    prf₂ : A m' → N m'
    prf₂ (inj₁ h₁)                = subst N (sym h₁) nzero
    prf₂ (inj₂ (m'' , h₁ , Am'')) = subst N (sym h₁) (nsucc Am'')

------------------------------------------------------------------------------
-- The induction principle for N *with* the hypothesis N n in the
-- induction step.
N-ind₁ : (A : D → Set) →
         A zero →
         (∀ {n} → N n → A n → A (succ₁ n)) →
         ∀ {n} → N n → A n
N-ind₁ A A0 is {n} Nn = N-least-pre-fixed A prf Nn
  where
  prf : n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n
  prf (inj₁ h)              = subst A (sym h) A0
  prf (inj₂ (n' , h , An')) = subst A (sym h) (is helper An')
    where
    helper : N n'
    helper with N-post-fixed Nn
    ... | inj₁ n≡0 = ⊥-elim (0≢S (trans (sym n≡0) h))
    ... | inj₂ (m' , h₁ , Nm') = subst N (succInjective (trans (sym h₁) h)) Nm'

------------------------------------------------------------------------------
-- The induction principle for N *without* the hypothesis N n in the
-- induction step.
N-ind₂ : (A : D → Set) →
         A zero →
         (∀ {n} → A n → A (succ₁ n)) →
         ∀ {n} → N n → A n
N-ind₂ A A0 is {n} = N-least-pre-fixed A prf
  where
  prf : n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n
  prf (inj₁ h)              = subst A (sym h) A0
  prf (inj₂ (n' , h , An')) = subst A (sym h) (is An')

------------------------------------------------------------------------------
-- Example: We will use N-least-pre-fixed as the induction principle on N.

postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero    + d ≡ d
  +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = N-least-pre-fixed A prf Nm
  where
  A : D → Set
  A i = N (i + n)

  prf : m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
  prf (inj₁ h) = subst N (cong (flip _+_ n) (sym h)) A0
    where
    A0 : A zero
    A0 = subst N (sym (+-leftIdentity n)) Nn
  prf (inj₂ (m' , m≡Sm' , Am')) =
    subst N (cong (flip _+_ n) (sym m≡Sm')) (is Am')
    where
    is : ∀ {i} → A i → A (succ₁ i)
    is {i} ih = subst N (sym (+-Sx i n)) (nsucc ih)

------------------------------------------------------------------------------
-- From/to N as a least fixed-point to/from N as data type.

open import FOTC.Data.Nat.Type renaming
  ( N to N'
  ; nsucc to nsucc'
  ; nzero to nzero'
  )

N'→N : ∀ {n} → N' n → N n
N'→N nzero'      = nzero
N'→N (nsucc' Nn) = nsucc (N'→N Nn)

-- Using N-ind₁.
N-→N' : ∀ {n} → N n → N' n
N-→N' = N-ind₁ N' nzero' (λ _ → nsucc')

-- Using N-ind₂.
N-→N'₁ : ∀ {n} → N n → N' n
N-→N'₁ = N-ind₂ N' nzero' nsucc'
