------------------------------------------------------------------------------
-- Equivalent approaches for implement the inductive predicate N
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.EquivalenceInductivePredicateN where

open import FOTC.Base

------------------------------------------------------------------------------
-- Using succ : D instead of succ₁ : D → D.

module Constant where

  module LFP where

    NatF : (D → Set) → D → Set
    NatF A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n')

    postulate
      N         : D → Set
      N-in-ho   : ∀ {n} → NatF N n → N n
      N-ind'-ho : (A : D → Set) → (∀ {n} → NatF A n → A n) → ∀ {n} → N n → A n

    N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ N n') → N n
    N-in = N-in-ho

    N-ind' : (A : D → Set) →
             (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n') → A n) →
             ∀ {n} → N n → A n
    N-ind' = N-ind'-ho

    --------------------------------------------------------------------------
    -- The data constructors of N using LFP.

    nzero : N zero
    nzero = N-in (inj₁ refl)

    nsucc : ∀ {n} → N n → N (succ · n)
    nsucc Nn = N-in (inj₂ (_ , refl , Nn))

    --------------------------------------------------------------------------
    -- The induction principle of N using LFP.
    N-ind : (A : D → Set) →
            A zero →
            (∀ {n} → A n → A (succ · n)) →
            ∀ {n} → N n → A n
    N-ind A A0 h = N-ind' A h'
      where
      h' : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ · m' ∧ A m') → A m
      h' (inj₁ m≡0)              = subst A (sym m≡0) A0
      h' (inj₂ (m' , prf , Am')) = subst A (sym prf) (h Am')

  ----------------------------------------------------------------------------
  module Data where

    data N : D → Set where
      nzero : N zero
      nsucc : ∀ {n} → N n → N (succ · n)

    N-ind : (A : D → Set) →
            A zero →
            (∀ {n} → A n → A (succ · n)) →
            ∀ {n} → N n → A n
    N-ind A A0 h nzero      = A0
    N-ind A A0 h (nsucc Nn) = h (N-ind A A0 h Nn)

    --------------------------------------------------------------------------
    -- The introduction rule of N using data.
    N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ N n') → N n
    N-in {n} h = case prf₁ prf₂ h
      where
      prf₁ : n ≡ zero → N n
      prf₁ n≡0 = subst N (sym n≡0) nzero

      prf₂ : ∃[ n' ] n ≡ succ · n' ∧ N n' → N n
      prf₂ (n' , prf , Nn') = subst N (sym prf) (nsucc Nn')

    --------------------------------------------------------------------------
    -- The induction principle for N using data.
    N-ind' :
      (A : D → Set) →
      (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ · n' ∧ A n') → A n) →
      ∀ {n} → N n → A n
    N-ind' A h = N-ind A h₁ h₂
      where
      h₁ :  A zero
      h₁ = h (inj₁ refl)

      h₂ : ∀ {m} → A m → A (succ · m)
      h₂ {m} Am = h (inj₂ (m , refl , Am))

------------------------------------------------------------------------------
-- Using succ₁ : D → D instead of succ : D.

module UnaryFunction where

  module LFP where

    NatF : (D → Set) → D → Set
    NatF A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')

    postulate
      N         : D → Set
      N-in-ho   : ∀ {n} → NatF N n → N n
      N-ind'-ho : (A : D → Set) → (∀ {n} → NatF A n → A n) → ∀ {n} → N n → A n

    N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n
    N-in = N-in-ho

    N-ind' : (A : D → Set) →
             (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
             ∀ {n} → N n → A n
    N-ind' = N-ind'-ho

    --------------------------------------------------------------------------
    -- The data constructors of N using LFP.

    nzero : N zero
    nzero = N-in (inj₁ refl)

    nsucc : ∀ {n} → N n → N (succ₁ n)
    nsucc Nn = N-in (inj₂ (_ , refl , Nn))

    --------------------------------------------------------------------------
    -- The induction principle of N using LFP.
    N-ind : (A : D → Set) →
            A zero →
            (∀ {n} → A n → A (succ₁ n)) →
            ∀ {n} → N n → A n
    N-ind A A0 h = N-ind' A h'
      where
      h' : ∀ {m} → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ A m') → A m
      h' (inj₁ m≡0)              = subst A (sym m≡0) A0
      h' (inj₂ (m' , prf , Am')) = subst A (sym prf) (h Am')

  ----------------------------------------------------------------------------
  module Data where

    data N : D → Set where
      nzero : N zero
      nsucc : ∀ {n} → N n → N (succ₁ n)

    N-ind : (A : D → Set) →
            A zero →
            (∀ {n} → A n → A (succ₁ n)) →
            ∀ {n} → N n → A n
    N-ind A A0 h nzero      = A0
    N-ind A A0 h (nsucc Nn) = h (N-ind A A0 h Nn)

    --------------------------------------------------------------------------
    -- The introduction rule of N using data.
    N-in : ∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') → N n
    N-in {n} h = case prf₁ prf₂ h
      where
      prf₁ : n ≡ zero → N n
      prf₁ n≡0 = subst N (sym n≡0) nzero

      prf₂ : ∃[ n' ] n ≡ succ₁ n' ∧ N n' → N n
      prf₂ (n' , prf , Nn') = subst N (sym prf) (nsucc Nn')

    --------------------------------------------------------------------------
    -- The induction principle for N using data.
    N-ind' :
      (A : D → Set) →
      (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
      ∀ {n} → N n → A n
    N-ind' A h = N-ind A h₁ h₂
      where
      h₁ :  A zero
      h₁ = h (inj₁ refl)

      h₂ : ∀ {m} → A m → A (succ₁ m)
      h₂ {m} Am = h (inj₂ (m , refl , Am))

module EsikProposition2Dot1 where

  postulate
    N : D → Set

    N-ind' : (A : D → Set) →
             (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n') → A n) →
             ∀ {n} → N n → A n
