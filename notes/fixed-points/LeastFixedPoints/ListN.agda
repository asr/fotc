------------------------------------------------------------------------------
-- From ListN as the least fixed-point to ListN using data
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We want to represent the total lists of total natural numbers data
-- type
--
-- data ListN : D → Set where
--   lnnil  : ListN []
--   lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
--
-- using the representation of ListN as the least fixed-point.

module LeastFixedPoints.ListN where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- ListN is a least fixed-point of a functor

-- The functor.
-- ListNF : (D → Set) → D → Set
-- ListNF P ns = ns ≡ [] ∨ (∃[ n' ] ∃[ ns' ] N n' ∧ ns ≡ n' ∷ ns' ∧ P ns')

-- List is the least fixed-point of ListF.
postulate
  ListN : D → Set

  -- ListN is a pre-fixed point of ListNF.
  --
  -- Peter: It corresponds to the introduction rules.
  ListN-in : ∀ {ns} →
             ns ≡ [] ∨ (∃[ n' ] ∃[ ns' ] N n' ∧ ns ≡ n' ∷ ns' ∧ ListN ns') →
             ListN ns

  -- ListN is the least pre-fixed point of ListFN.
  --
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  ListN-ind :
    (A : D → Set) →
    (∀ {ns} → ns ≡ [] ∨ (∃[ n' ] ∃[ ns' ] N n' ∧ ns ≡ n' ∷ ns' ∧ A ns') → A ns) →
    ∀ {ns} → ListN ns → A ns

------------------------------------------------------------------------------
-- The data constructors of List.
lnnil : ListN []
lnnil = ListN-in (inj₁ refl)

lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
lncons {n} {ns} Nn LNns = ListN-in (inj₂ (n , ns , Nn , refl , LNns))

------------------------------------------------------------------------------
-- The induction principle for List.
ListN-ind' : (A : D → Set) →
             A [] →
             (∀ n {ns} → N n → A ns → A (n ∷ ns)) →
             ∀ {ns} → ListN ns → A ns
ListN-ind' A A[] is = ListN-ind A prf
  where
  prf : ∀ {ns} → ns ≡ [] ∨ (∃[ n' ] ∃[ ns' ] N n' ∧ ns ≡ n' ∷ ns'  ∧ A ns') →
        A ns
  prf (inj₁ ns≡[])                        = subst A (sym ns≡[]) A[]
  prf (inj₂ (n' , ns' , Nn' , h₁ , Ans')) = subst A (sym h₁) (is n' Nn' Ans')

------------------------------------------------------------------------------
-- Example

ys : D
ys = 0' ∷ 1' ∷ 2' ∷ []

ys-ListN : ListN ys
ys-ListN =
  lncons nzero (lncons (nsucc nzero) (lncons (nsucc (nsucc nzero)) lnnil))
