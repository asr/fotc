------------------------------------------------------------------------------
-- Equivalence: N as the least fixed-point and N using Agda's data constructor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LeastFixedPoints.N where

open import FOTC.Base hiding ( pred-0 ; pred-S )
open import FOTC.Base.PropertiesI hiding ( predCong )

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
  NatF A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n')

  -- The natural numbers are the least fixed-point of NatF.
  postulate
    N : D → Set

    -- N is a pre-fixed point of NatF.
    --
    -- Peter: It corresponds to the introduction rules.
    N-ir : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ N n') → N n

    -- The higher-order version.
    N-ir-ho : ∀ {n} → NatF N n → N n

    -- N is the least pre-fixed point of NatF.
    --
    -- Peter: It corresponds to the elimination rule of an inductively
    -- defined predicate.
    N-least-pre-fixed :
      (A : D → Set) →
      (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n') → A n) →
      ∀ {n} → N n → A n

    -- Higher-order version.
    N-least-pre-fixed-ho :
      (A : D → Set) → (∀ {n} → NatF A n → A n) → ∀ {n} → N n → A n

  ----------------------------------------------------------------------------
  -- From/to N-ir/N-ir-ho.

  N-ir₁ : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ N n') → N n
  N-ir₁ = N-ir-ho

  N-ir-ho₁ : ∀ {n} → NatF N n → N n
  N-ir-ho₁ = N-ir₁

  ----------------------------------------------------------------------------
  -- From/to N-least-pre-fixed/N-least-pre-fixed-ho

  N-least-pre-fixed' :
    (A : D → Set) →
    (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n') → A n) →
    ∀ {n} → N n → A n
  N-least-pre-fixed' = N-least-pre-fixed-ho

  N-least-pre-fixed-ho' :
    (A : D → Set) → (∀ {n} → NatF A n → A n) → ∀ {n} → N n → A n
  N-least-pre-fixed-ho' = N-least-pre-fixed

  ----------------------------------------------------------------------------
  -- The data constructors of N.
  nzero : N zero
  nzero = N-ir (inj₁ refl)

  nsucc : ∀ {n} → N n → N (succ · n)
  nsucc Nn = N-ir (inj₂ (_ , refl , Nn))

  ----------------------------------------------------------------------------
  -- Because N is the least pre-fixed point of NatF (i.e. N-in and
  -- N-ind), we can proof that N is also a post-fixed point of NatF.

  -- N is a post-fixed point of NatF.
  N-post-fixed : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ N n')
  N-post-fixed = N-least-pre-fixed A h
    where
    A : D → Set
    A m = m ≡ zero ∨ (∃[ m' ] m ≡ succ · m' ∧ N m')

    h : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ · m' ∧ A m') → A m
    h (inj₁ m≡0)              = inj₁ m≡0
    h (inj₂ (m' , prf , Am')) = inj₂ (m' , prf , helper Am')
      where
      helper : A m' → N m'
      helper (inj₁ prf')                = subst N (sym prf') nzero
      helper (inj₂ (m'' , prf' , Am'')) = subst N (sym prf') (nsucc Am'')

  ----------------------------------------------------------------------------
  -- The induction principle for N *with* the hypothesis N n in the
  -- induction step using N-least-pre-fixed.

  N-ind₁ : (A : D → Set) →
           A zero →
           (∀ {n} → N n → A n → A (succ · n)) →
           ∀ {n} → N n → A n
  N-ind₁ A A0 h Nn = ∧-proj₂ (N-least-pre-fixed B h' Nn)
    where
    B : D → Set
    B n = N n ∧ A n

    h' : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ · m' ∧ B m') → B m
    h' (inj₁ m≡0) = subst B (sym m≡0) (nzero , A0)
    h' (inj₂ (m' , prf , Nm' , Am')) =
      (subst N (sym prf) (nsucc Nm')) , subst A (sym prf) (h Nm' Am')

  ----------------------------------------------------------------------------
  -- The induction principle for N *without* the hypothesis N n in the
  -- induction step using N-least-pre-fixed

  N-ind₂ : (A : D → Set) →
           A zero →
           (∀ {n} → A n → A (succ · n)) →
           ∀ {n} → N n → A n
  N-ind₂ A A0 h = N-least-pre-fixed A h'
    where
    h' : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ · m' ∧ A m') → A m
    h' (inj₁ m≡0)              = subst A (sym m≡0) A0
    h' (inj₂ (m' , prf , Am')) = subst A (sym prf) (h Am')

  ----------------------------------------------------------------------------
  -- Example: We will use N-least-pre-fixed as the induction
  -- principle on N.

  postulate
    _+_  : D → D → D
    +-0x : ∀ d → zero + d         ≡ d
    +-Sx : ∀ d e → (succ · d) + e ≡ succ · (d + e)

  +-leftIdentity : ∀ n → zero + n ≡ n
  +-leftIdentity n = +-0x n

  +-N : ∀ {m n} → N m → N n → N (m + n)
  +-N {n = n} Nm Nn = N-least-pre-fixed A h Nm
    where
    A : D → Set
    A i = N (i + n)

    h : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ · m' ∧ A m') → A m
    h (inj₁ m≡0) = subst N (cong (flip _+_ n) (sym m≡0)) A0
      where
      A0 : A zero
      A0 = subst N (sym (+-leftIdentity n)) Nn
    h (inj₂ (m' , prf , Am')) =
      subst N (cong (flip _+_ n) (sym prf)) (is Am')
      where
      is : ∀ {i} → A i → A (succ · i)
      is {i} Ai = subst N (sym (+-Sx i n)) (nsucc Ai)

  ----------------------------------------------------------------------------
  -- Example: A proof using N-post-fixed.

  postulate
    pred-0 : pred · zero             ≡ zero
    pred-S : ∀ n → pred · (succ · n) ≡ n

  predCong : ∀ {m n} → m ≡ n → pred · m ≡ pred · n
  predCong refl = refl

  pred-N : ∀ {n} → N n → N (pred · n)
  pred-N {n} Nn = case h₁ h₂ (N-post-fixed Nn)
    where
    h₁ : n ≡ zero → N (pred · n)
    h₁ n≡0 = subst N (sym (trans (predCong n≡0) pred-0)) nzero

    h₂ : ∃[ n' ] n ≡ succ · n' ∧ N n' → N (pred · n)
    h₂ (n' , prf , Nn') = subst N (sym (trans (predCong prf) (pred-S n'))) Nn'

  ----------------------------------------------------------------------------
  -- From/to N as a least fixed-point to/from N as data type.

  data N' : D → Set where
    nzero' : N' zero
    nsucc' : ∀ {n} → N' n → N' (succ · n)

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
    nsucc : ∀ {n} → N n → N (succ · n)

  -- The induction principle for N *with* the hypothesis N n in the
  -- induction step.
  N-ind₁ : (A : D → Set) →
           A zero →
           (∀ {n} → N n → A n → A (succ · n)) →
           ∀ {n} → N n → A n
  N-ind₁ A A0 h nzero      = A0
  N-ind₁ A A0 h (nsucc Nn) = h Nn (N-ind₁ A A0 h Nn)

  -- The induction principle for N *without* the hypothesis N n in the
  -- induction step.
  N-ind₂ : (A : D → Set) →
           A zero →
           (∀ {n} → A n → A (succ · n)) →
           ∀ {n} → N n → A n
  N-ind₂ A A0 h nzero      = A0
  N-ind₂ A A0 h (nsucc Nn) = h (N-ind₂ A A0 h Nn)

  ----------------------------------------------------------------------------
  -- N-ir.

  N-ir : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ N n') → N n
  N-ir {n} h = case prf₁ prf₂ h
    where
    prf₁ : n ≡ zero → N n
    prf₁ n≡0 = subst N (sym n≡0) nzero

    prf₂ : ∃[ n' ] n ≡ succ · n' ∧ N n' → N n
    prf₂ (n' , prf , Nn') = subst N (sym prf) (nsucc Nn')

  ----------------------------------------------------------------------------
  -- From N-ind₂ to N-least-pre-fixed.

  N-least-pre-fixed₂ :
    (A : D → Set) →
    (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n') → A n) →
    ∀ {n} → N n → A n
  N-least-pre-fixed₂ A h = N-ind₂ A h₁ h₂
    where
    h₁ :  A zero
    h₁ = h (inj₁ refl)

    h₂ : ∀ {m} → A m → A (succ · m)
    h₂ {m} Am = h (inj₂ (m , refl , Am))

------------------------------------------------------------------------------
-- References
--
-- Ésik, Z. (2009). Fixed Point Theory. In: Handbook of Weighted
-- Automata. Ed. by Droste, M., Kuich, W. and Vogler, H. Monographs in
-- Theoretical Computer Science. An EATCS Series. Springer. Chap. 2.
