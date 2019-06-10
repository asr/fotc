------------------------------------------------------------------------------
-- Equivalence: N as the least fixed-point and N using Agda's data constructor
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LFPs.N where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Properties

------------------------------------------------------------------------------
-- Auxiliary definitions and properties

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

cong : (f : D → D) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------------
module LFP where

  infixl 9 _+_

  -- N is a least fixed-point of a functor

  -- The functor.
  NatF : (D → Set) → D → Set
  NatF A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')

  -- The natural numbers are the least fixed-point of NatF.
  postulate
    N : D → Set

    -- N is a pre-fixed point of NatF, i.e.
    --
    -- NatF N ≤ N.
    --
    -- Peter: It corresponds to the introduction rules.
    N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n

    -- The higher-order version.
    N-in-ho : ∀ {n} → NatF N n → N n

    -- N is the least pre-fixed point of NatF, i.e.
    --
    -- ∀ A. NatF A ≤ A ⇒ N ≤ A.
    --
    -- Peter: It corresponds to the elimination rule of an inductively
    -- defined predicate.
    N-ind :
      (A : D → Set) →
      (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
      ∀ {n} → N n → A n

    -- Higher-order version.
    N-ind-ho :
      (A : D → Set) → (∀ {n} → NatF A n → A n) → ∀ {n} → N n → A n

  ----------------------------------------------------------------------------
  -- N-in and N-in-ho are equivalents

  N-in₁ : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n
  N-in₁ = N-in-ho

  N-in-ho₁ : ∀ {n} → NatF N n → N n
  N-in-ho₁ = N-in₁

  ----------------------------------------------------------------------------
  -- N-ind and N-ind-ho are equivalents

  N-ind-fo :
    (A : D → Set) →
    (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
    ∀ {n} → N n → A n
  N-ind-fo = N-ind-ho

  N-ind-ho' :
    (A : D → Set) → (∀ {n} → NatF A n → A n) → ∀ {n} → N n → A n
  N-ind-ho' = N-ind

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
  N-out : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
  N-out = N-ind A h
    where
    A : D → Set
    A m = m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')

    h : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
    h (inj₁ m≡0)              = inj₁ m≡0
    h (inj₂ (m' , prf , Am')) = inj₂ (m' , prf , helper Am')
      where
      helper : A m' → N m'
      helper (inj₁ prf')                = subst N (sym prf') nzero
      helper (inj₂ (m'' , prf' , Am'')) = subst N (sym prf') (nsucc Am'')

  -- The higher-order version.
  N-out-ho : ∀ {n} → N n → NatF N n
  N-out-ho = N-out

  ----------------------------------------------------------------------------
  -- The induction principle for N *with* the hypothesis N n in the
  -- induction step using N-ind.

  N-ind₁ : (A : D → Set) →
           A zero →
           (∀ {n} → N n → A n → A (succ₁ n)) →
           ∀ {n} → N n → A n
  N-ind₁ A A0 h Nn = ∧-proj₂ (N-ind B h' Nn)
    where
    B : D → Set
    B n = N n ∧ A n

    h' : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ B m') → B m
    h' (inj₁ m≡0) = subst B (sym m≡0) (nzero , A0)
    h' (inj₂ (m' , prf , Nm' , Am')) =
      (subst N (sym prf) (nsucc Nm')) , subst A (sym prf) (h Nm' Am')

  ----------------------------------------------------------------------------
  -- The induction principle for N *without* the hypothesis N n in the
  -- induction step using N-ind

  N-ind₂ : (A : D → Set) →
           A zero →
           (∀ {n} → A n → A (succ₁ n)) →
           ∀ {n} → N n → A n
  N-ind₂ A A0 h = N-ind A h'
    where
    h' : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
    h' (inj₁ m≡0)              = subst A (sym m≡0) A0
    h' (inj₂ (m' , prf , Am')) = subst A (sym prf) (h Am')

  ----------------------------------------------------------------------------
  -- Example: We will use N-ind as the induction principle on N.

  postulate
    _+_  : D → D → D
    +-0x : ∀ d → zero + d        ≡ d
    +-Sx : ∀ d e → (succ₁ d) + e ≡ succ₁ (d + e)

  +-leftIdentity : ∀ n → zero + n ≡ n
  +-leftIdentity n = +-0x n

  +-N : ∀ {m n} → N m → N n → N (m + n)
  +-N {n = n} Nm Nn = N-ind A h Nm
    where
    A : D → Set
    A i = N (i + n)

    h : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
    h (inj₁ m≡0) = subst N (cong (flip _+_ n) (sym m≡0)) A0
      where
      A0 : A zero
      A0 = subst N (sym (+-leftIdentity n)) Nn
    h (inj₂ (m' , prf , Am')) =
      subst N (cong (flip _+_ n) (sym prf)) (is Am')
      where
      is : ∀ {i} → A i → A (succ₁ i)
      is {i} Ai = subst N (sym (+-Sx i n)) (nsucc Ai)

  ----------------------------------------------------------------------------
  -- Example: A proof using N-out.

  pred-N : ∀ {n} → N n → N (pred₁ n)
  pred-N {n} Nn = case h₁ h₂ (N-out Nn)
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
  N-ind₁ A A0 h nzero      = A0
  N-ind₁ A A0 h (nsucc Nn) = h Nn (N-ind₁ A A0 h Nn)

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
  -- From N-ind₂ to N-ind.

  N-ind' :
    (A : D → Set) →
    (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
    ∀ {n} → N n → A n
  N-ind' A h = N-ind₂ A h₁ h₂
    where
    h₁ :  A zero
    h₁ = h (inj₁ refl)

    h₂ : ∀ {m} → A m → A (succ₁ m)
    h₂ {m} Am = h (inj₂ (m , refl , Am))
