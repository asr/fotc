-- Tested with Agda 2.2.11 on 11 October 2011.

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
-- 1. f d ≤ d               -- d is a pre-fixed point of f
-- 2. ∀ e. f e ≤ e ⇒ d ≤ e  -- d is the least prefixed-point of f

-- Least fixed-point : d is the least fixed-point of f if
-- 1. f d = d               -- d is a fixed-point of f
-- 2. ∀ e. f e ≤ e ⇒ d ≤ e  -- d is the least prefixed-point of f

-- Thm: If d is the least pre-fixed point of f, then d is a fixed
-- point of f (TODO: source).

------------------------------------------------------------------------------
-- Auxiliary definitions

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

------------------------------------------------------------------------------
-- N is a least pre-fixed point of a functor

-- Instead defining the least pre-fixed via a (higher-order)
-- operator, we will define it using an instance of that operator.

-- The functor
-- NatF : (D → Set) → D → Set
-- NatF X n = n ≡ zero ∨ (∃ λ m → n ≡ succ m ∧ X m)

-- The natural numbers are the least pre-fixed point of NatF.
postulate
  N : D → Set

  -- N is pre-fixed point of NatF.
  -- Peter: It corresponds to the introduction rules.
  N-lfp₁ : ∀ n → n ≡ zero ∨ (∃ λ m → n ≡ succ₁ m ∧ N m) → N n

  -- N is the least prefixed-point of NatF.
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  N-lfp₂ : ∀ (P : D → Set) {n} →
           (n ≡ zero ∨ (∃ λ m → n ≡ succ₁ m ∧ P m) → P n) →
           N n → P n

------------------------------------------------------------------------------
-- The data constructors of N.
zN : N zero
zN = N-lfp₁ zero (inj₁ refl)

sN : ∀ {n} → N n → N (succ₁ n)
sN {n} Nn = N-lfp₁ (succ₁ n) (inj₂ (n , (refl , Nn)))

------------------------------------------------------------------------------
-- Because N is the least pre-fixed point of NatF (i.e. N-lfp₁ and
-- N-lfp₂), we can proof that N is also post-fixed point of NatF.

-- N is a post-fixed point of NatF.
N-lfp₃ : ∀ {n} → N n → n ≡ zero ∨ (∃ λ m → n ≡ succ₁ m ∧ N m)
N-lfp₃ {n} Nn = N-lfp₂ P prf Nn
  where
  P : D → Set
  P x = x ≡ zero ∨ ∃ λ m → x ≡ succ₁ m ∧ N m

  prf : n ≡ zero ∨ ∃ (λ m → n ≡ succ₁ m ∧ P m) → P n
  prf h = [ inj₁ , (λ h₁ → inj₂ (prf₁ h₁)) ] h
    where
    prf₁ : ∃ (λ m → n ≡ succ₁ m ∧ (m ≡ zero ∨ ∃ (λ m' → m ≡ succ₁ m' ∧ N m'))) →
           ∃ λ m → n ≡ succ₁ m ∧ N m
    prf₁ (m , n=Sm , h₂) = m , n=Sm , prf₂ h₂
      where
      prf₂ : m ≡ zero ∨ ∃ (λ m' → m ≡ succ₁ m' ∧ N m') → N m
      prf₂ h₂ = [ (λ h₃ → subst N (sym h₃) zN) , prf₃ ] h₂
        where
        prf₃ : ∃ (λ m' → m ≡ succ₁ m' ∧ N m') → N m
        prf₃ (m' , m≡Sm' , Nm') = subst N (sym m≡Sm') (sN Nm')

------------------------------------------------------------------------------
-- The induction principle for N.
indN : (P : D → Set) →
       P zero →
       (∀ {n} → P n → P (succ₁ n)) →
       ∀ {n} → N n → P n
indN P P0 is {n} Nn = N-lfp₂ P [ prf₁ , prf₂ ] Nn
  where
  prf₁ : n ≡ zero → P n
  prf₁ n≡0 = subst P (sym n≡0) P0

  prf₂ : ∃ (λ m → n ≡ succ₁ m ∧ P m) → P n
  prf₂ (m , n≡Sm , Pm) = subst P (sym n≡Sm) (is Pm)

------------------------------------------------------------------------------
-- Example: We will use N-lfp₂ as the induction principle on N.
postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero    + d ≡ d
  +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = N-lfp₂ P prf Nm

  where
  P : D → Set
  P i = N (i + n)

  prf : m ≡ zero ∨ ∃ (λ m' → m ≡ succ₁ m' ∧ P m') → P m
  prf h = [ prf₁ , prf₂ ] h
    where
    P0 : P zero
    P0 = subst N (sym (+-leftIdentity n)) Nn

    prf₁ : m ≡ zero → P m
    prf₁ h₁ = subst N (cong (flip _+_ n) (sym h₁)) P0

    is : ∀ {i} → P i → P (succ₁ i)
    is {i} Pi = subst N (sym (+-Sx i n)) (sN Pi)

    prf₂ : ∃ (λ m' → m ≡ succ₁ m' ∧ P m') → P m
    prf₂ (m' , m≡Sm' , Pm') = subst N (cong (flip _+_ n) (sym m≡Sm')) (is Pm')
