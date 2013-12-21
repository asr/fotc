------------------------------------------------------------------------------
-- Equivalence: N as the least fixed-point and N using Agda's data constructor
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LeastFixedPoints.N where

open import FOTC.Base
open import FOTC.Base.PropertiesI

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
module LFP where

  -- N is a least fixed-point of a functor

  -- The functor.
  NatF : (D → Set) → D → Set
  NatF A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')

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

    -- Higher-order version (incomplete?).
    N-least-pre-fixed-ho :
      ∀ (A : D → Set) {n} →
      (NatF A n → A n) →
      N n → A n

  ----------------------------------------------------------------------------
  -- From/to N-in/N-in-ho.

  N-in₁ : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n
  N-in₁ = N-in-ho

  N-in-ho₁ : ∀ {n} → NatF N n → N n
  N-in-ho₁ = N-in₁

  ----------------------------------------------------------------------------
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

  ----------------------------------------------------------------------------
  -- The data constructors of N.
  nzero : N zero
  nzero = N-in (inj₁ refl)

  nsucc : ∀ {n} → N n → N (succ₁ n)
  nsucc Nn = N-in (inj₂ (_ , refl , Nn))

  ----------------------------------------------------------------------------
  -- Because N is the least pre-fixed point of NatF (i.e. N-in and
  -- N-ind), we can proof that N is also a post-fixed point of NatF.

  -- N is a post-fixed point of NatF.
  N-post-fixed : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
  N-post-fixed = N-least-pre-fixed A h
    where
    A : D → Set
    A m = m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')

    h : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
    h (inj₁ prf)              = inj₁ prf
    h (inj₂ (m' , prf , Am')) = inj₂ (m' , prf , helper Am')
      where
      helper : A m' → N m'
      helper (inj₁ prf')                = subst N (sym prf') nzero
      helper (inj₂ (m'' , prf' , Am'')) = subst N (sym prf') (nsucc Am'')

  ----------------------------------------------------------------------------
  -- The induction principle for N *with* the hypothesis N n in the
  -- induction step.

  N-ind₁ : (A : D → Set) →
           A zero →
           (∀ {n} → N n → A n → A (succ₁ n)) →
           ∀ {n} → N n → A n
  N-ind₁ A A0 is {n} Nn = N-least-pre-fixed A h Nn
    where
    h : n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n
    h (inj₁ prf)              = subst A (sym prf) A0
    h (inj₂ (n' , prf , An')) = subst A (sym prf) (is helper An')
      where
      helper : N n'
      helper with N-post-fixed Nn
      ... | inj₁ n≡0 = ⊥-elim (0≢S (trans (sym n≡0) prf))
      ... | inj₂ (m' , prf' , Nm') =
        subst N (succInjective (trans (sym prf') prf)) Nm'

  ----------------------------------------------------------------------------
  -- The induction principle for N *without* the hypothesis N n in the
  -- induction step.

  N-ind₂ : (A : D → Set) →
           A zero →
           (∀ {n} → A n → A (succ₁ n)) →
           ∀ {n} → N n → A n
  N-ind₂ A A0 is {n} = N-least-pre-fixed A h
    where
    h : n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n
    h (inj₁ prf)              = subst A (sym prf) A0
    h (inj₂ (n' , prf , An')) = subst A (sym prf) (is An')

  ----------------------------------------------------------------------------
  -- Example: We will use N-least-pre-fixed as the induction principle on N.

  postulate
    _+_  : D → D → D
    +-0x : ∀ d → zero + d      ≡ d
    +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)

  +-leftIdentity : ∀ n → zero + n ≡ n
  +-leftIdentity n = +-0x n

  +-N : ∀ {m n} → N m → N n → N (m + n)
  +-N {m} {n} Nm Nn = N-least-pre-fixed A h Nm
    where
    A : D → Set
    A i = N (i + n)

    h : m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
    h (inj₁ prf) = subst N (cong (flip _+_ n) (sym prf)) A0
      where
      A0 : A zero
      A0 = subst N (sym (+-leftIdentity n)) Nn
    h (inj₂ (m' , m≡Sm' , Am')) =
      subst N (cong (flip _+_ n) (sym m≡Sm')) (is Am')
      where
      is : ∀ {i} → A i → A (succ₁ i)
      is {i} Ai = subst N (sym (+-Sx i n)) (nsucc Ai)

  ----------------------------------------------------------------------------
  -- Example: A proof using N-post-fixed.

  pred-N : ∀ {n} → N n → N (pred₁ n)
  pred-N {n} Nn = case h₁ h₂ (N-post-fixed Nn)
    where
    h₁ : n ≡ zero → N (pred₁ n)
    h₁ n≡0 = subst N (sym (trans (predCong n≡0) pred-0)) nzero

    h₂ : ∃[ n' ] n ≡ succ₁ n' ∧ N n' → N (pred₁ n)
    h₂ (n' , prf , Nn') = subst N (sym (trans (predCong prf) (pred-S n'))) Nn'

  ----------------------------------------------------------------------------
  -- From/to N as a least fixed-point to/from N as data type.

  data N' : D → Set where
    nzero' : N' zero
    nsucc' : ∀ {n} → N' n → N' (succ₁ n)

  N'→N : ∀ {n} → N' n → N n
  N'→N nzero'      = nzero
  N'→N (nsucc' Nn) = nsucc (N'→N Nn)

  -- Using N-ind₁.
  N→N' : ∀ {n} → N n → N' n
  N→N' = N-ind₁ N' nzero' (λ _ → nsucc')

  -- Using N-ind₂.
  N→N'₁ : ∀ {n} → N n → N' n
  N→N'₁ = N-ind₂ N' nzero' nsucc'

------------------------------------------------------------------------------
module Data where

  data N : D → Set where
    nzero : N zero
    nsucc : ∀ {n} → N n → N (succ₁ n)

  -- The induction principle for N *with* the hypothesis N n in the
  -- induction step.
  N-ind₁ : (A : D → Set) →
           A zero →
           (∀ {n} → N n → A n → A (succ₁ n)) →
           ∀ {n} → N n → A n
  N-ind₁ A A0 is nzero      = A0
  N-ind₁ A A0 is (nsucc Nn) = is Nn (N-ind₁ A A0 is Nn)

  -- The induction principle for N *without* the hypothesis N n in the
  -- induction step.
  N-ind₂ : (A : D → Set) →
           A zero →
           (∀ {n} → A n → A (succ₁ n)) →
           ∀ {n} → N n → A n
  N-ind₂ A A0 h nzero      = A0
  N-ind₂ A A0 h (nsucc Nn) = h (N-ind₂ A A0 h Nn)

  ----------------------------------------------------------------------------
  -- N-in.

  N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n
  N-in {n} h = case prf₁ prf₂ h
    where
    prf₁ : n ≡ zero → N n
    prf₁ n≡0 = subst N (sym n≡0) nzero

    prf₂ : ∃[ n' ] n ≡ succ₁ n' ∧ N n' → N n
    prf₂ (n' , prf , Nn') = subst N (sym prf) (nsucc Nn')

  ----------------------------------------------------------------------------
  -- From N-ind₂ to N-least-pre-fixed.

  N→0∨S : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
  N→0∨S = N-ind₂ A A0 is
    where
    A : D → Set
    A i = i ≡ zero ∨ (∃[ i' ] i ≡ succ₁ i' ∧ N i')

    A0 : A zero
    A0 = inj₁ refl

    is : ∀ {i} → A i → A (succ₁ i)
    is {i} Ai = case prf₁ prf₂ Ai
      where
      prf₁ : i ≡ zero → succ₁ i ≡ zero ∨ (∃[ i' ] succ₁ i ≡ succ₁ i' ∧ N i')
      prf₁ h' = inj₂ (i , refl , (subst N (sym h') nzero))

      prf₂ : ∃[ i' ] i ≡ succ₁ i' ∧ N i' →
             succ₁ i ≡ zero ∨ (∃[ i' ] succ₁ i ≡ succ₁ i' ∧ N i')
      prf₂ (i' , prf , Ni') = inj₂ (i , refl , subst N (sym prf) (nsucc Ni'))

  N-least-pre-fixed₂ :
    ∀ (A : D → Set) {n} →
    (n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
    N n → A n
  N-least-pre-fixed₂ A {n} h Nn = case prf₁ prf₂ (N→0∨S Nn)
    where
    prf₁ : n ≡ zero → A n
    prf₁ n≡0 = h (inj₁ n≡0)

    prf₂ : ∃[ n' ] n ≡ succ₁ n' ∧ N n' → A n
    prf₂ (n' , prf , Nn') = h (inj₂ (n' , prf , {!!}))
