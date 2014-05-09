------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality.Type
open import FOTC.Data.Colist
open import FOTC.Data.Colist.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream

-----------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Stream predicate is also a pre-fixed point of the functional
-- StreamF, i.e.
--
-- StreamF Stream ≤ Stream (see FOTC.Data.Stream.Type).
Stream-in : ∀ {xs} →
            ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs' →
            Stream xs
Stream-in h = Stream-coind A h' h
  where
  A : D → Set
  A xs = ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs'

  h' : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h' (x' , xs' , prf , Sxs') = x' , xs' , prf , Stream-out Sxs'

zeros-Stream : Stream zeros
zeros-Stream = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ zeros

  h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h Axs = zero , zeros , trans Axs zeros-eq , refl

ones-Stream : Stream ones
ones-Stream = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ ones

  h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h Axs = succ₁ zero , ones , trans Axs ones-eq , refl

∷-Stream : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
∷-Stream {x} {xs} h = ∷-Stream-helper (Stream-out h)
  where
  ∷-Stream-helper : ∃[ x' ] ∃[ xs' ] x ∷ xs ≡ x' ∷ xs' ∧ Stream xs' →
                    Stream xs
  ∷-Stream-helper (x' , xs' , prf , Sxs') =
    subst Stream (sym (∧-proj₂ (∷-injective prf))) Sxs'

-- Version using Agda with constructor.
∷-Stream' : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
∷-Stream' h with Stream-out h
... | x' , xs' , prf , Sxs' =
  subst Stream (sym (∧-proj₂ (∷-injective prf))) Sxs'

Stream→Colist : ∀ {xs} → Stream xs → Colist xs
Stream→Colist {xs} Sxs = Colist-coind A h₁ h₂
  where
  A : D → Set
  A ys = Stream ys

  h₁ : ∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')
  h₁ Axs with Stream-out Axs
  ... | x' , xs' , prf , Sxs' = inj₂ (x' , xs' , prf , Sxs')

  h₂ : A xs
  h₂ = Sxs

-- Adapted from (Sander 1992, p. 59).
streamLength : ∀ {xs} → Stream xs → length xs ≈ ∞
streamLength {xs} Sxs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = ∃[ xs ] Stream xs ∧ m ≡ length xs ∧ n ≡ ∞

  h₁ : ∀ {m n} → R m n →
       m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  h₁ {m} {n} (xs , Sxs , m=lxs , n≡∞) = helper₁ (Stream-out Sxs)
    where
    helper₁ : (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs') →
              m ≡ zero ∧ n ≡ zero
                ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
    helper₁ (x' , xs' , xs≡x'∷xs' , Sxs') =
      inj₂ (length xs'
           , ∞
           , helper₂
           , trans n≡∞ ∞-eq
           , (xs' , Sxs' , refl , refl))
        where
        helper₂ : m ≡ succ₁ (length xs')
        helper₂ = trans m=lxs (trans (lengthCong xs≡x'∷xs') (length-∷ x' xs'))

  h₂ : R (length xs) ∞
  h₂ = xs , Sxs , refl , refl

-- Adapted from (Sander 1992, p. 59). Version using Agda with
-- constructor.
streamLength' : ∀ {xs} → Stream xs → length xs ≈ ∞
streamLength' {xs} Sxs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = ∃[ xs ] Stream xs ∧ m ≡ length xs ∧ n ≡ ∞

  h₁ : ∀ {m n} → R m n →
       m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  h₁ {m} (xs , Sxs , m=lxs , n≡∞) with Stream-out Sxs
  ... | x' , xs' , xs≡x'∷xs' , Sxs' =
    inj₂ (length xs' , ∞ , helper , trans n≡∞ ∞-eq , (xs' , Sxs' , refl , refl))
    where
    helper : m ≡ succ₁ (length xs')
    helper = trans m=lxs (trans (lengthCong xs≡x'∷xs') (length-∷ x' xs'))

  h₂ : R (length xs) ∞
  h₂ = xs , Sxs , refl , refl

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
