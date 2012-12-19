------------------------------------------------------------------------------
-- From List using postulates to List using data
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LeastFixedPoints.List where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- List is a least fixed-point of a functor

-- The functor.
-- ListF : (D → Set) → D → Set
-- ListF P xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] P xs' ∧ xs ≡ x' ∷ xs')

-- List is the least fixed-point of ListF.
postulate
  List : D → Set

  -- List is a pre-fixed point of ListF.
  --
  -- Peter: It corresponds to the introduction rules.
  List-in : ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] List xs' ∧ xs ≡ x' ∷ xs') →
            List xs

  -- List is the least pre-fixed point of ListF.
  --
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  List-ind :
    (A : D → Set) →
    (∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A xs' ∧ xs ≡ x' ∷ xs') → A xs) →
    ∀ {xs} → List xs → A xs

------------------------------------------------------------------------------
-- The data constructors of List.
lnil : List []
lnil = List-in (inj₁ refl)

lcons : ∀ x {xs} → List xs → List (x ∷ xs)
lcons x {xs} Lxs = List-in (inj₂ (x , xs , Lxs , refl))

------------------------------------------------------------------------------
-- The induction principle for List.
indList : (A : D → Set) →
          A [] →
          (∀ x {xs} → A xs → A (x ∷ xs)) →
          ∀ {xs} → List xs → A xs
indList A A[] h Lxs = List-ind A (case prf₁ prf₂) Lxs
  where
  prf₁ : ∀ {xs} → xs ≡ [] → A xs
  prf₁ h = subst A (sym h) A[]

  prf₂ : ∀ {xs} → (∃[ x' ] ∃[ xs' ] A xs' ∧ xs ≡ x' ∷ xs') → A xs
  prf₂ (x' , xs' , Axs' , h₁) = subst A (sym h₁) (h x' Axs')
