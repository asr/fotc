{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT on 12 March 2012.

module LeastFixedPoints where

open import FOTC.Base
open import FOTC.Base.PropertiesI

infixl 9 _+_

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
-- Auxiliary definitions

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

------------------------------------------------------------------------------
-- N is a least fixed-point of a functor

-- Instead defining the least fixed-point via a (higher-order)
-- operator, we will define it using an instance of that operator.

-- The functor
NatF : (D → Set) → D → Set
NatF P n = n ≡ zero ∨ (∃[ m ] n ≡ succ₁ m ∧ P m)

-- The natural numbers are the least fixed-point of NatF.
postulate
  N : D → Set

  -- N is a pre-fixed point of NatF.
  --
  -- Peter: It corresponds to the introduction rules.
  N-lfp₁    : ∀ {n} → n ≡ zero ∨ (∃[ m ] n ≡ succ₁ m ∧ N m) → N n
  -- N-lfp₁ : ∀ n → NatF N n → N n  -- Higher-order version

  -- N is a the least pre-fixed point of NatF.
  --
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  N-lfp₂    : (A : D → Set) →
              (∀ {n} → n ≡ zero ∨ (∃[ m ] n ≡ succ₁ m ∧ A m) → A n) →
              ∀ {n} → N n → A n
  -- N-lfp₂ : (A : D → Set) →  -- Higher-order version
  --          (∀ {n} → NatF A n → A n) →
  --          ∀ {n} → N n → A n

------------------------------------------------------------------------------
-- The data constructors of N.
zN : N zero
zN = N-lfp₁ (inj₁ refl)

sN : ∀ {n} → N n → N (succ₁ n)
sN Nn = N-lfp₁ (inj₂ (_ , (refl , Nn)))

------------------------------------------------------------------------------
-- Because N is the least pre-fixed point of NatF (i.e. N-lfp₁ and
-- N-lfp₂), we can proof that N is also a post-fixed point of NatF.

-- N is a post-fixed point of NatF.
N-lfp₃ : ∀ {n} → N n → n ≡ zero ∨ (∃ λ m → n ≡ succ₁ m ∧ N m)
N-lfp₃ Nn = N-lfp₂ A prf Nn
  where
  A : D → Set
  A x = x ≡ zero ∨ ∃ λ m → x ≡ succ₁ m ∧ N m

  prf : ∀ {n'} → n' ≡ zero ∨ ∃ (λ m → n' ≡ succ₁ m ∧ A m) → A n'
  prf {n'} h = [ inj₁ , (λ h₁ → inj₂ (prf₁ h₁)) ] h
    where
    prf₁ : ∃ (λ m → n' ≡ succ₁ m ∧ (m ≡ zero ∨ ∃ (λ m' → m ≡ succ₁ m' ∧ N m'))) →
           ∃ λ m → n' ≡ succ₁ m ∧ N m
    prf₁ (m , n'=Sm , h₂) = m , n'=Sm , prf₂ h₂
      where
      prf₂ : m ≡ zero ∨ ∃ (λ m' → m ≡ succ₁ m' ∧ N m') → N m
      prf₂ h₂ = [ (λ h₃ → subst N (sym h₃) zN) , prf₃ ] h₂
        where
        prf₃ : ∃ (λ m' → m ≡ succ₁ m' ∧ N m') → N m
        prf₃ (_ , m≡Sm' , Nm') = subst N (sym m≡Sm') (sN Nm')

------------------------------------------------------------------------------
-- The induction principle for N *without* the hypothesis N n in the
-- induction step.
indN₁ : (A : D → Set) →
       A zero →
       (∀ {n} → A n → A (succ₁ n)) →
       ∀ {n} → N n → A n
indN₁ A A0 is Nn = N-lfp₂ A [ prf₁ , prf₂ ] Nn
  where
  prf₁ : ∀ {n'} → n' ≡ zero → A n'
  prf₁ n'≡0 = subst A (sym n'≡0) A0

  prf₂ : ∀ {n'} → ∃ (λ m → n' ≡ succ₁ m ∧ A m) → A n'
  prf₂ (_ , n'≡Sm , Am) = subst A (sym n'≡Sm) (is Am)

-- The induction principle for N *with* the hypothesis N n in the
-- induction step.
--
-- 2012-03-06. We cannot proof this principle because N-lfp₂ does not
-- have the hypothesis N n.
--
-- indN₂ : (A : D → Set) →
--        A zero →
--        (∀ {n} → N n → A n → A (succ₁ n)) →
--        ∀ {n} → N n → A n
-- indN₂ A A0 is Nn = N-lfp₂ A [ prf₁ , prf₂ ] Nn
--   where
--   prf₁ : ∀ {n'} → n' ≡ zero → A n'
--   prf₁ n'≡0 = subst A (sym n'≡0) A0

--   prf₂ : ∀ {n'} → ∃ (λ m → n' ≡ succ₁ m ∧ A m) → A n'
--   prf₂ {n'} (m , n'≡Sm , Am) = subst A (sym n'≡Sm) (is helper Am)
--     where
--     helper : N m
--     helper = [ prf₃ , prf₄ ] (N-lfp₃ {!!})
--       where
--       prf₃ : n' ≡ zero → N m
--       prf₃ n'≡0 = ⊥-elim (0≢S (trans (sym n'≡0) n'≡Sm))

--       prf₄ : ∃ (λ m' → n' ≡ succ₁ m' ∧ N m') → N m
--       prf₄ (_ , n'≡Sm' , Nm') =
--         subst N (succInjective (trans (sym n'≡Sm') n'≡Sm)) Nm'

------------------------------------------------------------------------------
-- Example: We will use N-lfp₂ as the induction principle on N.
postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero    + d ≡ d
  +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = N-lfp₂ A prf Nm
  where
  A : D → Set
  A i = N (i + n)

  prf : ∀ {m'} → m' ≡ zero ∨ ∃ (λ m'' → m' ≡ succ₁ m'' ∧ A m'') → A m'
  prf h = [ prf₁ , prf₂ ] h
    where
    A0 : A zero
    A0 = subst N (sym (+-leftIdentity n)) Nn

    prf₁ : ∀ {m} → m ≡ zero → A m
    prf₁ h₁ = subst N (cong (flip _+_ n) (sym h₁)) A0

    is : ∀ {i} → A i → A (succ₁ i)
    is {i} ih = subst N (sym (+-Sx i n)) (sN ih)

    prf₂ : ∀ {m} → ∃ (λ m'' → m ≡ succ₁ m'' ∧ A m'') → A m
    prf₂ (_ , m≡Sm'' , Am'') =
      subst N (cong (flip _+_ n) (sym m≡Sm'')) (is Am'')
