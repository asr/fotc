------------------------------------------------------------------------------
-- From N using postulates to N using data
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LeastFixedPoints.N where

open import FOTC.Base

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

-- Instead of defining the least fixed-point via a (higher-order)
-- operator, we will define it using an instance of that operator.

-- The functor.
-- NatF : (D → Set) → D → Set
-- NatF P n = n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')

-- The natural numbers are the least fixed-point of NatF.
postulate
  N : D → Set

  -- N is a pre-fixed point of NatF.
  --
  -- Peter: It corresponds to the introduction rules.
  N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] N n' ∧ n ≡ succ₁ n') → N n
  -- N-in : ∀ n → NatF N n → N n  -- Higher-order version

  -- N is the least pre-fixed point of NatF.
  --
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  N-ind : (A : D → Set) →
          (∀ {n} → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n') → A n) →
          ∀ {n} → N n → A n

------------------------------------------------------------------------------
-- The data constructors of N.
nzero : N zero
nzero = N-in (inj₁ refl)

nsucc : ∀ {n} → N n → N (succ₁ n)
nsucc Nn = N-in (inj₂ (_ , (Nn , refl)))

------------------------------------------------------------------------------
-- Because N is the least pre-fixed point of NatF (i.e. N-in and
-- N-ind), we can proof that N is also a post-fixed point of NatF.

-- N is a post-fixed point of NatF.
N-lfp₃ : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] N n' ∧ n ≡ succ₁ n')
N-lfp₃ Nn = N-ind A prf Nn
  where
  A : D → Set
  A x = x ≡ zero ∨ (∃[ n' ] N n' ∧ x ≡ succ₁ n')

  prf : ∀ {n''} → n'' ≡ zero ∨ (∃[ n' ] A n' ∧ n'' ≡ succ₁ n') → A n''
  prf {n''} h = case inj₁ ((λ h₁ → inj₂ (prf₁ h₁))) h -- case inj₁ prf₁ h
    where
    prf₁ : (∃[ n' ] A n' ∧ n'' ≡ succ₁ n') → ∃[ n' ] N n' ∧ n'' ≡ succ₁ n'
    prf₁ (n' , An' , n''=Sn') = n' , prf₂ An' , n''=Sn'
      where
      prf₂ : A n' → N n'
      prf₂ An' = case (λ ah → subst N (sym ah) nzero) prf₃ An'
        where
        prf₃ : (∃[ m' ] N m' ∧ n' ≡ succ₁ m') → N n'
        prf₃ (_ , Nm' , m≡Sm' ) = subst N (sym m≡Sm') (nsucc Nm')

------------------------------------------------------------------------------
-- The induction principle for N *without* the hypothesis N n in the
-- induction step.
indN : (A : D → Set) →
        A zero →
        (∀ {n} → A n → A (succ₁ n)) →
        ∀ {n} → N n → A n
indN A A0 h Nn = N-ind A (case prf₁ prf₂) Nn
  where
  prf₁ : ∀ {n'} → n' ≡ zero → A n'
  prf₁ n'≡0 = subst A (sym n'≡0) A0

  prf₂ : ∀ {n'} → (∃[ n'' ] A n'' ∧ n' ≡ succ₁ n'') → A n'
  prf₂ (_ , An'' , n'≡Sn'') = subst A (sym n'≡Sn'') (h An'')

-- The induction principle for N *with* the hypothesis N n in the
-- induction step.
--
-- 2012-03-06. We cannot proof this principle because N-ind does not
-- have the hypothesis N n.
--
-- indN₂ : (A : D → Set) →
--        A zero →
--        (∀ {n} → N n → A n → A (succ₁ n)) →
--        ∀ {n} → N n → A n
-- indN₂ A A0 is Nn = N-ind A [ prf₁ , prf₂ ] Nn
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
-- Example: We will use N-ind as the induction principle on N.
postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero    + d ≡ d
  +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = N-ind A prf Nm
  where
  A : D → Set
  A i = N (i + n)

  prf : ∀ {m'} → m' ≡ zero ∨ (∃[ m'' ] A m'' ∧ m' ≡ succ₁ m'') → A m'
  prf h = case prf₁ prf₂ h
    where
    A0 : A zero
    A0 = subst N (sym (+-leftIdentity n)) Nn

    prf₁ : ∀ {m} → m ≡ zero → A m
    prf₁ h₁ = subst N (cong (flip _+_ n) (sym h₁)) A0

    is : ∀ {i} → A i → A (succ₁ i)
    is {i} ih = subst N (sym (+-Sx i n)) (nsucc ih)

    prf₂ : ∀ {m} → (∃[ m'' ] A m'' ∧ m ≡ succ₁ m'') → A m
    prf₂ (_ ,  Am'' , m≡Sm'') =
      subst N (cong (flip _+_ n) (sym m≡Sm'')) (is Am'')

------------------------------------------------------------------------------
-- From/to N as a least fixed-point to/from N as data type.

open import FOTC.Data.Nat.Type renaming
  ( N to N'
  ; N-ind to N-ind'
  ; nsucc to nsucc'
  ; nzero to nzero'
  )

thm₁ : ∀ {n} → N' n → N n
thm₁ nzero' = nzero
thm₁ (nsucc' Nn) = nsucc (thm₁ Nn)

thm₂ : ∀ {n} → N n → N' n
thm₂ Nn = indN N' nzero' nsucc' Nn
