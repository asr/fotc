------------------------------------------------------------------------------
-- The FOTC types without using data, i.e. using Agda as a logical framework
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Predicates where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Base.PropertiesI

------------------------------------------------------------------------------
-- The existential proyections.

∃-proj₁ : ∀ {A} → ∃ A → D
∃-proj₁ (x , _) = x

∃-proj₂ : ∀ {A} → (h : ∃ A) → A (∃-proj₁ h)
∃-proj₂ (_ , Ax) = Ax

------------------------------------------------------------------------------
-- The inductive FOTC types using postulates.

module Pure where

  -- The FOTC natural numbers type.
  postulate
    N     : D → Set
    nzero : N zero
    nsucc : ∀ {n} → N n → N (succ₁ n)

  -- Example.
  [1] : D
  [1] = succ₁ zero

  1-N : N [1]
  1-N = nsucc nzero

  -- The FOTC lists type.
  postulate
    List  : D → Set
    lnil  : List []
    lcons : ∀ x {xs} → List xs → List (x ∷ xs)

  -- Example.
  l : List (zero ∷ true ∷ [])
  l = lcons zero (lcons true lnil)

  -- The FOTC list of natural numbers type.
  postulate
    ListN  : D → Set
    lnnil  : ListN []
    lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

  -- Example.
  ln : ListN (zero ∷ [1] ∷ [])
  ln = lncons nzero (lncons 1-N lnnil)

------------------------------------------------------------------------------
-- The inductive FOTC types using data.

module Inductive where

  -- The FOTC natural numbers type.
  data N : D → Set where
    nzero : N zero
    nsucc : ∀ {n} → N n → N (succ₁ n)

  -- Example.
  [1] : D
  [1] = succ₁ zero

  1-N : N [1]
  1-N = nsucc nzero

  -- The FOTC lists type.
  data List : D → Set where
    lnil  : List []
    lcons : ∀ x {xs} → List xs → List (x ∷ xs)

  -- Example.
  l : List (zero ∷ true ∷ [])
  l = lcons zero (lcons true lnil)

  -- The FOTC list of natural numbers type.
  data ListN : D → Set where
    lnnil  : ListN []
    lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

  -- Example.
  ln : ListN (zero ∷ [1] ∷ [])
  ln = lncons nzero (lncons 1-N lnnil)

------------------------------------------------------------------------------
-- The least fixed-point operator.

module LFP where

  postulate
    -- Least fixed-points correspond to inductively defined types.
    --
    -- N.B. We cannot write μ in first-order logic. We should use an
    -- instance instead.
    μ : ((D → Set) → D → Set) → D → Set

    -- In FOTC, we cannot use the equality on predicates, i.e. we
    -- cannot write
    --
    -- (f : (D → Set) → D → Set) → f (μ f) ≡ μ f  (1)
    --
    -- because the type of the equality is
    --
    -- _≡_ : D → D → Set,
    --
    -- therefore we postulate both directions of the conversion rule (1).

    -- LFP₁ : (f : (D → Set) → D → Set)(d : D) → μ f d → f (μ f) d
    μ-in : (f : (D → Set) → D → Set)(d : D) → f (μ f) d → μ f d

------------------------------------------------------------------------------
-- The greatest fixed-point operator.

-- N.B. At the moment, the definitions of μ and ν are the same.

module GFP where

  postulate
    -- Greatest fixed-points correspond to co-inductively defined
    -- types.

    ν : ((D → Set) → D → Set) → D → Set

    ν-out : (f : (D → Set) → D → Set)(d : D) → ν f d → f (ν f) d
    GFP₂  : (f : (D → Set) → D → Set)(d : D) → f (ν f) d → ν f d

------------------------------------------------------------------------------
-- The FOTC natural numbers type as the least fixed-point of a
-- functor.

module NLFP where

  open LFP

  -- Functor for the FOTC natural numbers type.

  -- From Peter: NatF if D was an inductive type.
  --
  -- NatF : (D → Set) → D → Set
  -- NatF X zero      = ⊤
  -- NatF X (succ₁ n) = X n

  -- From Peter: NatF in pure predicate logic.
  NatF : (D → Set) → D → Set
  NatF X n = n ≡ zero ∨ (∃[ n' ] (n ≡ succ₁ n' ∧ X n'))

  -- The FOTC natural numbers type using μ.
  N : D → Set
  N = μ NatF

  -- The data constructors of N.
  nzero : N zero
  nzero = μ-in NatF zero (inj₁ refl)

  nsucc : {n : D} → N n → N (succ₁ n)
  nsucc {n} Nn = μ-in NatF (succ₁ n) (inj₂ (n , refl , Nn))

  -- Example.
  [1] : D
  [1] = succ₁ zero

  1-N : N [1]
  1-N = nsucc nzero

------------------------------------------------------------------------------
-- The FOTC list type as the least fixed-point of a functor.

module ListLFT where

  open LFP

  -- Functor for the FOTC lists type.
  ListF : (D → Set) → D → Set
  ListF X xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] (xs ≡ x' ∷ xs' ∧ X xs'))

  -- The FOTC list type using μ.
  List : D → Set
  List = μ ListF

  -- The data constructors of List.
  lnil : List []
  lnil = μ-in ListF [] (inj₁ refl)

  lcons : ∀ x {xs} → List xs → List (x ∷ xs)
  lcons x {xs} Lxs = μ-in ListF (x ∷ xs) (inj₂ (x , xs , refl , Lxs))

  -- Example.
  l : List (zero ∷ true ∷ [])
  l = lcons zero (lcons true lnil)

------------------------------------------------------------------------------
-- The FOTC list of natural numbers type as the least fixed-point of a
-- functor.

module ListNLFT where

  open LFP
  open NLFP

  -- Functor for the FOTC list of natural numbers type.
  ListNF : (D → Set) → D → Set
  ListNF X ns = ns ≡ [] ∨ (∃[ n' ] ∃[ ns' ] (ns ≡ n' ∷ ns' ∧ N n' ∧ X ns'))

  -- The FOTC list type using μ.
  ListN : D → Set
  ListN = μ ListNF

  -- The data constructors of ListN.
  lnnil : ListN []
  lnnil = μ-in ListNF [] (inj₁ refl)

  lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
  lncons {n} {ns} Nn LNns =
    μ-in ListNF (n ∷ ns) (inj₂ (n , ns , refl , Nn , LNns))

  -- Example.
  ln : ListN (zero ∷ [1] ∷ [])
  ln = lncons nzero (lncons 1-N lnnil)

------------------------------------------------------------------------------
-- The FOTC Colist type as the greatest fixed-point of a functor.

module CoList where

  open GFP

  -- Functor for the FOTC Colists type (the same functor that for the
  -- List type).
  ColistF : (D → Set) → D → Set
  ColistF X xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] (xs ≡ x' ∷ xs' ∧ X xs'))

  -- The FOTC Colist type using ν.
  Colist : D → Set
  Colist = ν ColistF

  -- The data constructors of Colist.
  nilCL : Colist []
  nilCL = GFP₂ ColistF [] (inj₁ refl)

  consCL : ∀ x xs → Colist xs → Colist (x ∷ xs)
  consCL x xs CLxs = GFP₂ ColistF (x ∷ xs) (inj₂ (x , xs , refl , CLxs))

  -- Example (finite colist).
  l : Colist (zero ∷ true ∷ [])
  l = consCL zero (true ∷ []) (consCL true [] nilCL)

  -- TODO: Example (infinite colist).
  -- zerosCL : Colist {!!}
  -- zerosCL = consCL zero {!!} zerosCL

------------------------------------------------------------------------------
-- The FOTC Stream type as the greatest fixed-point of a functor.

module Stream where

  open GFP

  -- Functor for the FOTC Stream type.
  StreamF : (D → Set) → D → Set
  StreamF X xs = ∃[ x' ] ∃[ xs' ] (xs ≡ x' ∷ xs' ∧ X xs')

  -- The FOTC Stream type using ν.
  Stream : D → Set
  Stream = ν StreamF

  -- The data constructor of Stream.
  consS : ∀ x {xs} → Stream xs → Stream (x ∷ xs)
  consS x {xs} Sxs = GFP₂ StreamF (x ∷ xs) (x , xs , refl , Sxs)

  -- TODO: Example
  -- zerosS : Stream {!!}
  -- zerosS = consS zero {!!} zerosS

  headS : ∀ {x xs} → Stream (x ∷ xs) → D
  headS {x} _ = x

  tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
  tailS {x} {xs} Sx∷xs = Sxs
    where
    unfoldS : StreamF (ν StreamF) (x ∷ xs)
    unfoldS = ν-out StreamF (x ∷ xs) Sx∷xs

    e : D
    e = ∃-proj₁ unfoldS

    Pe : ∃ λ es → x ∷ xs ≡ e ∷ es ∧ ν StreamF es
    Pe = ∃-proj₂ unfoldS

    es : D
    es = ∃-proj₁ Pe

    Pes : x ∷ xs ≡ e ∷ es ∧ ν StreamF es
    Pes = ∃-proj₂ Pe

    xs≡es : xs ≡ es
    xs≡es = ∧-proj₂ (∷-injective (∧-proj₁ Pes))

    Sxs : ν StreamF xs
    Sxs = subst (ν StreamF) (sym xs≡es) (∧-proj₂ Pes)
