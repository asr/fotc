------------------------------------------------------------------------------
-- From List as the least fixed-point to List using data
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We want to represent the total lists data type
--
-- data List : D → Set where
--   lnil  : List []
--   lcons : ∀ x {xs} → List xs → List (x ∷ xs)
--
-- using the representation of List as the least fixed-point.

module LeastFixedPoints.List where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.UnaryNumbers

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
indList A A[] is = List-ind A h
  where
  h : ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A xs' ∧ xs ≡ x' ∷ xs') → A xs
  h (inj₁ xs≡[])                  = subst A (sym xs≡[]) A[]
  h (inj₂ (x' , xs' , Axs' , h₁)) = subst A (sym h₁) (is x' Axs')

------------------------------------------------------------------------------
-- Example

xs : D
xs = [0] ∷ true ∷ [1] ∷ false ∷ []

xs-List : List xs
xs-List = lcons [0] (lcons true (lcons [1] (lcons false lnil)))
