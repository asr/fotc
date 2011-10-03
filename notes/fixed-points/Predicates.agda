-- Tested with Agda 2.2.11 on 03 October 2011.

module Predicates where

open import FOTC.Base

open import FOTC.Base.PropertiesI

------------------------------------------------------------------------------

-- The FOTC types without use data, i.e. using Agda as a logical framework.

module Pure where

  -- The FOTC natural numbers type.
  postulate
    N  : D → Set
    zN : N zero
    sN : ∀ {n} → N n → N (succ n)

  -- Example.
  one : D
  one = succ zero

  oneN : N one
  oneN = sN zN

  -- The FOTC lists type.
  postulate
    List  : D → Set
    nilL  : List []
    consL : ∀ x {xs} → List xs → List (x ∷ xs)

  -- Example
  l : List (zero ∷ true ∷ [])
  l = consL zero (consL true nilL)

  -- The FOTC list of natural numbers type.
  postulate
    ListN  : D → Set
    nilLN  : ListN []
    consLN : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

  -- Example.
  ln : ListN (zero ∷ one ∷ [])
  ln = consLN zN (consLN oneN nilLN)

------------------------------------------------------------------------------

-- The inductive FOTC types using data.

module Inductive where

  -- The FOTC natural numbers type.
  data N : D → Set where
    zN : N zero
    sN : ∀ {n} → N n → N (succ n)

  -- Example.
  one : D
  one = succ zero

  oneN : N one
  oneN = sN zN

  -- The FOTC lists type.
  data List : D → Set where
    nilL  :                      List []
    consL : ∀ x {xs} → List xs → List (x ∷ xs)

  -- Example
  l : List (zero ∷ true ∷ [])
  l = consL zero (consL true nilL)

  -- The FOTC list of natural numbers type.
  data ListN : D → Set where
    nilLN  :                             ListN []
    consLN : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

  -- Example.
  ln : ListN (zero ∷ one ∷ [])
  ln = consLN zN (consLN oneN nilLN)

------------------------------------------------------------------------------

-- The least fixed-point operator.

module LFP where

  postulate
    -- Least fixed-points correspond to inductively defined types.
    --
    -- N.B. We cannot write LFP in first order logic. We should use an
    -- instance instead.
    LFP : ((D → Set) → D → Set) → D → Set

    -- In FOTC, we cannot use the equality on predicates, i.e. we
    -- cannot write
    --
    -- (f : (D → Set) → D → Set) → f (LFP f) ≡ LFP f  (1)
    --
    -- because the type of the equality is
    --
    -- _≡_ : D → D → Set,
    --
    -- therefore we postulate both directions of the conversion rule (1).

    LFP₁ : (f : (D → Set) → D → Set)(d : D) → LFP f d → f (LFP f) d
    LFP₂ : (f : (D → Set) → D → Set)(d : D) → f (LFP f) d → LFP f d

------------------------------------------------------------------------------

-- The greatest fixed-point operator.

-- N.B. At the moment, the definitions of LFP and GFP are the same.

module GFP where

  postulate
    -- Greatest fixed-points correspond to coinductively defined types.

    GFP : ((D → Set) → D → Set) → D → Set

    GFP₁ : (f : (D → Set) → D → Set)(d : D) → GFP f d → f (GFP f) d
    GFP₂ : (f : (D → Set) → D → Set)(d : D) → f (GFP f) d → GFP f d

------------------------------------------------------------------------------

-- The FOTC natural numbers type as the least fixed-point of a
-- functor.

module NLFP where

  open LFP

  -- Functor for the FOTC natural numbers type.

  -- From Peter: NatF if D was an inductive type
  -- NatF : (D → Set) → D → Set
  -- NatF X zero     = ⊤
  -- NatF X (succ n) = X n

  -- From Peter: NatF in pure predicate logic.
  NatF : (D → Set) → D → Set
  NatF X n = n ≡ zero ∨ (∃ λ m → n ≡ succ m ∧ X m)

  -- The FOTC natural numbers type using LFP.
  N : D → Set
  N = LFP NatF

  -- The data constructors of N.
  zN : N zero
  zN = LFP₂ NatF zero (inj₁ refl)

  sN : {n : D} → N n → N (succ n)
  sN {n} Nn = LFP₂ NatF (succ n) (inj₂ (n , (refl , Nn)))

  -- Example.
  one : D
  one = succ zero

  oneN : N one
  oneN = sN zN

------------------------------------------------------------------------------

-- The FOTC list type as the least fixed-point of a functor.

module ListLFT where

  open LFP

  -- Functor for the FOTC lists type.
  ListF : (D → Set) → D → Set
  ListF X ds = ds ≡ [] ∨ (∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ X es)

  -- The FOTC list type using LFP.
  List : D → Set
  List = LFP ListF

  -- The data constructors of List.
  nilL : List []
  nilL = LFP₂ ListF [] (inj₁ refl)

  consL : ∀ x {xs} → List xs → List (x ∷ xs)
  consL x {xs} Lxs = LFP₂ ListF (x ∷ xs) (inj₂ (x , xs , refl , Lxs))

  -- Example.
  l : List (zero ∷ true ∷ [])
  l = consL zero (consL true nilL)

------------------------------------------------------------------------------

-- The FOTC list of natural numbers type as the least fixed-point of a
-- functor.

module ListNLFT where

  open LFP
  open NLFP

  -- Functor for the FOTC list of natural numbers type.
  ListNF : (D → Set) → D → Set
  ListNF X ds = ds ≡ [] ∨ (∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ N e ∧ X es)

  -- The FOTC list type using LFP.
  ListN : D → Set
  ListN = LFP ListNF

  -- The data constructors of ListN.
  nilLN : ListN []
  nilLN = LFP₂ ListNF [] (inj₁ refl)

  consLN : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
  consLN {n} {ns} Nn LNns =
    LFP₂ ListNF (n ∷ ns) (inj₂ (n , ns , refl , Nn , LNns))

  -- Example.
  ln : ListN (zero ∷ one ∷ [])
  ln = consLN zN (consLN oneN nilLN)

------------------------------------------------------------------------------

-- The FOTC Colist type as the greatest fixed-point of a functor.

module CoList where

  open GFP

  -- Functor for the FOTC Colists type (the same functor that for the
  -- List type).
  ColistF : (D → Set) → D → Set
  ColistF X ds = ds ≡ [] ∨ (∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ X es)

  -- The FOTC Colist type using GFP.
  Colist : D → Set
  Colist = GFP ColistF

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

module Stream₁ where

  open GFP

  -- Functor for the FOTC Stream type.
  StreamF : (D → Set) → D → Set
  StreamF X ds = ∃ λ e → X ds

  -- The FOTC Stream type using GFP.
  Stream : D → Set
  Stream = GFP StreamF

  -- The data constructor of Stream.
  -- Using StreamF we cannot define this data constructor
  -- consS : ∀ x xs → Stream xs → Stream (x ∷ xs)
  -- consS x xs Sxs = GFP₂ StreamF (x ∷ xs) {!!}

------------------------------------------------------------------------------

-- The FOTC Stream type as the greatest fixed-point of a functor.

module Stream₂ where

  open GFP

  -- Functor for the FOTC Stream type.
  StreamF : (D → Set) → D → Set
  StreamF X ds = ∃ λ e → ∃ λ es → X es

  -- The FOTC Stream type using GFP.
  Stream : D → Set
  Stream = GFP StreamF

  -- The data constructor of Stream.
  -- TODO: To use implicit arguments.
  consS : ∀ x xs → Stream xs → Stream (x ∷ xs)
  consS x xs Sxs = GFP₂ StreamF (x ∷ xs) (x , xs , Sxs)

  -- TODO: Example
  -- zerosS : Stream {!!}
  -- zerosS = consS zero {!!} zerosS

  headS : ∀ {x xs} → Stream (x ∷ xs) → D
  headS {x} _ = x

  tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
  tailS {x} {xs} S = GFP₂ StreamF xs (x , x ∷ xs , S)

  -- The functor StreamF does not link together the parts of the
  -- stream, so I can get a stream from any stream.
  bad : ∀ {xs ys} → Stream xs → Stream ys
  bad {xs} {ys} S = GFP₂ StreamF ys (ys , xs , S)

------------------------------------------------------------------------------

-- The FOTC Stream type as the greatest fixed-point of a functor.

module Stream₃ where

  open GFP

  -- Functor for the FOTC Stream type.
  StreamF : (D → Set) → D → Set
  StreamF X ds = ∃ λ e → ∃ λ es → ds ≡ e ∷ es ∧ X es

  -- The FOTC Stream type using GFP.
  Stream : D → Set
  Stream = GFP StreamF

  -- The data constructor of Stream.
  -- TODO: To use implicit arguments.
  consS : ∀ x xs → Stream xs → Stream (x ∷ xs)
  consS x xs Sxs = GFP₂ StreamF (x ∷ xs) (x , xs , refl , Sxs)

  -- TODO: Example
  -- zerosS : Stream {!!}
  -- zerosS = consS zero {!!} zerosS

  headS : ∀ {x xs} → Stream (x ∷ xs) → D
  headS {x} _ = x

  tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
  tailS {x} {xs} Sx∷xs = Sxs
    where
    unfoldS : StreamF (GFP StreamF) (x ∷ xs)
    unfoldS = GFP₁ StreamF (x ∷ xs) Sx∷xs

    e : D
    e = ∃-proj₁ unfoldS

    Pe : ∃ λ es → x ∷ xs ≡ e ∷ es ∧ GFP StreamF es
    Pe = ∃-proj₂ unfoldS

    es : D
    es = ∃-proj₁ Pe

    Pes : x ∷ xs ≡ e ∷ es ∧ GFP StreamF es
    Pes = ∃-proj₂ Pe

    xs≡es : xs ≡ es
    xs≡es = ∧-proj₂ (∷-injective (∧-proj₁ Pes))

    Sxs : GFP StreamF xs
    Sxs = subst (GFP StreamF) (sym xs≡es) (∧-proj₂ Pes)
