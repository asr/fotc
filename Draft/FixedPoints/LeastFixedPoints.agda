module Draft.FixedPoints.LeastFixedPoints where

open import FOTC.Base

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
  N-lfp₁ : ∀ n → n ≡ zero ∨ (∃ λ m → n ≡ succ m ∧ N m) → N n

  -- N is the least prefixed-point of NatF.
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  N-lfp₂ : ∀ n (O : D → Set) → (n ≡ zero ∨ (∃ λ m → n ≡ succ m ∧ O m) → O n) →
           N n → O n

------------------------------------------------------------------------------
-- The data constructors of N.
zN : N zero
zN = N-lfp₁ zero (inj₁ refl)

sN : {n : D} → N n → N (succ n)
sN {n} Nn = N-lfp₁ (succ n) (inj₂ (n , (refl , Nn)))

------------------------------------------------------------------------------
-- Example: We will use N-lfp₂ as the induction principle on N.
postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero   + d ≡ d
  +-Sx : ∀ d e → succ d + e ≡ succ (d + e)

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = N-lfp₂ m P prf Nm

  where
  P : D → Set
  P i = N (i + n)

  prf : m ≡ zero ∨ ∃ (λ m' → m ≡ succ m' ∧ P m') → P m
  prf h = [ prf₁ , prf₂ ] h
    where
    P0 : P zero
    P0 = subst N (sym (+-leftIdentity Nn)) Nn

    prf₁ : m ≡ zero → P m
    prf₁ h₁ = subst N (cong (flip _+_ n) (sym h₁)) P0

    is : ∀ {i} → P i → P (succ i)
    is {i} Pi = subst N (sym (+-Sx i n)) (sN Pi)

    prf₂ : ∃ (λ m' → m ≡ succ m' ∧ P m') → P m
    prf₂ (m' , m≡Sm' , Pm') = subst N (cong (flip _+_ n) (sym m≡Sm')) (is Pm')

------------------------------------------------------------------------------
-- Because N is the least pre-fixed point of NatF (i.e. N-lfp₁ and
-- N-lfp₂), we can proof that N is also post-fixed point of NatF.

-- N is a post-fixed point of NatF.
N-lfp₃ : ∀ n → N n → n ≡ zero ∨ (∃ λ m → n ≡ succ m ∧ N m)
N-lfp₃ n Nn = N-lfp₂ n O prf Nn
  where
    O : D → Set
    O x = x ≡ zero ∨ (∃ λ m → x ≡ succ m ∧ N m)

    prf : n ≡ zero ∨ ∃ (λ m → n ≡ succ m ∧ O m) → O n
    prf h = [ inj₁ , (λ h₁ → inj₂ (prf₁ h₁)) ] h
      where
      prf₁ : ∃ (λ m → n ≡ succ m ∧ (m ≡ zero ∨ ∃ (λ m' → m ≡ succ m' ∧ N m'))) →
             ∃ (λ m → n ≡ succ m ∧ N m)
      prf₁ (m , n=Sm , h₂) = m , n=Sm , prf₂ h₂
        where
          prf₂ : m ≡ zero ∨ ∃ (λ m' → m ≡ succ m' ∧ N m') → N m
          prf₂ h₂ = [ (λ h₃ → subst N (sym h₃) zN) , prf₃ ] h₂
            where
              prf₃ : ∃ (λ m' → m ≡ succ m' ∧ N m') → N m
              prf₃ (m' , m≡Sm' , Nm') = subst N (sym m≡Sm') (sN Nm')
