------------------------------------------------------------------------------
-- Equivalence of definitions of total lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LeastFixedPoints.List where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
module LFP where

  -- List is a least fixed-point of a functor

  -- The functor.
  -- ListF : (D → Set) → D → Set
  -- ListF P xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ P xs')

  -- List is the least fixed-point of ListF.
  postulate
    List : D → Set

    -- List is a pre-fixed point of ListF.
    --
    -- Peter: It corresponds to the introduction rules.
    List-in : ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ List xs') →
              List xs

    -- List is the least pre-fixed point of ListF.
    --
    -- Peter: It corresponds to the elimination rule of an inductively
    -- defined predicate.
    List-least-pre-fixed :
      (A : D → Set) →
      (∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs') → A xs) →
      ∀ {xs} → List xs → A xs

  ----------------------------------------------------------------------------
  -- The data constructors of List.
  lnil : List []
  lnil = List-in (inj₁ refl)

  lcons : ∀ x {xs} → List xs → List (x ∷ xs)
  lcons x {xs} Lxs = List-in (inj₂ (x , xs , refl , Lxs))

  ----------------------------------------------------------------------------
  -- The induction principle for List.
  List-ind : (A : D → Set) →
             A [] →
             (∀ x {xs} → A xs → A (x ∷ xs)) →
             ∀ {xs} → List xs → A xs
  List-ind A A[] is = List-least-pre-fixed A prf
    where
    prf : ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs') → A xs
    prf (inj₁ xs≡[])                  = subst A (sym xs≡[]) A[]
    prf (inj₂ (x' , xs' , h₁ , Axs')) = subst A (sym h₁) (is x' Axs')

  ----------------------------------------------------------------------------
  -- Example

  xs : D
  xs = 0' ∷ true ∷ 1' ∷ false ∷ []

  xs-List : List xs
  xs-List = lcons 0' (lcons true (lcons 1' (lcons false lnil)))

------------------------------------------------------------------------------
module Data where

  data List : D → Set where
    lnil  : List []
    lcons : ∀ x {xs} → List xs → List (x ∷ xs)

  -- Induction principle.
  List-ind : (A : D → Set) →
             A [] →
             (∀ x {xs} → A xs → A (x ∷ xs)) →
             ∀ {xs} → List xs → A xs
  List-ind A A[] h lnil          = A[]
  List-ind A A[] h (lcons x Lxs) = h x (List-ind A A[] h Lxs)

  ----------------------------------------------------------------------------
  -- List-in

  List-in : ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ List xs') →
            List xs
  List-in {xs} h = case prf₁ prf₂ h
    where
    prf₁ : xs ≡ [] → List xs
    prf₁ xs≡[] = subst List (sym xs≡[]) lnil

    prf₂ : ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ List xs' → List xs
    prf₂ (x' , xs' , prf , Lxs') =  subst List (sym prf) (lcons x' Lxs')

  ----------------------------------------------------------------------------
  -- List-least-pre-fixed

  List-least-pre-fixed :
    (A : D → Set) →
    (∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs') → A xs) →
    ∀ {xs} → List xs → A xs
  List-least-pre-fixed A h Lxs = List-ind A h₁ h₂ Lxs
    where
    h₁ : A []
    h₁ = h (inj₁ refl)

    h₂ : ∀ y {ys} → A ys → A (y ∷ ys)
    h₂ y {ys} Ays = h (inj₂ (y , ys , refl , Ays))
