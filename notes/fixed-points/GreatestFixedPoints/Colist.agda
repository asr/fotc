------------------------------------------------------------------------------
-- Co-lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GreatestFixedPoints.Colist where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- Colist is a greatest fixed-point of a functor

-- The functor.
ColistF : (D → Set) → D → Set
ColistF A xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')

-- Colist is the greatest fixed-point of ColistF.
postulate
  Colist : D → Set

  -- Colist is a post-fixed point of ColistF, i.e.
  --
  -- Colist ≤ ColistF Colist.
  Colist-out-ho : ∀ {n} → Colist n → ColistF Colist n

  -- Colist is the greatest post-fixed point of ColistF, i.e.
  --
  -- ∀ A. A ≤ ColistF A ⇒ A ≤ Colist.
  Colist-coind-ho :
    (A : D → Set) →
    -- A is post-fixed point of ColistF.
    (∀ {xs} → A xs → ColistF A xs) →
    -- Colist is greater than A.
    ∀ {xs} → A xs → Colist xs

------------------------------------------------------------------------------
-- First-order versions

Colist-out : ∀ {xs} →
             Colist xs →
             xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')
Colist-out = Colist-out-ho

Colist-coind :
  (A : D → Set) →
  (∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')) →
  ∀ {xs} → A xs → Colist xs
Colist-coind = Colist-coind-ho

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Colist predicate is also a pre-fixed point of the functional
-- ColistF, i.e.
--
-- ColistF Colist ≤ Colist.
Colist-in-ho : ∀ {xs} → ColistF Colist xs → Colist xs
Colist-in-ho h = Colist-coind-ho A h' h
  where
  A : D → Set
  A xs = ColistF Colist xs

  h' : ∀ {xs} → A xs → ColistF A xs
  h' (inj₁ xs≡0) = inj₁ xs≡0
  h' (inj₂ (x' , xs' , prf , CLxs' )) =
    inj₂ (x' , xs' , prf , Colist-out CLxs')

-- The first-order version.
Colist-in : ∀ {xs} →
            xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs') →
            Colist xs
Colist-in = Colist-in-ho

------------------------------------------------------------------------------
-- A stronger co-induction principle
--
-- From (Paulson, 1997. p. 16).

postulate
  Colist-coind-stronger-ho :
    (A : D → Set) →
    (∀ {xs} → A xs → ColistF A xs ∨ Colist xs) →
    ∀ {xs} → A xs → Colist xs

Colist-coind-ho' :
  (A : D → Set) →
  (∀ {xs} → A xs → ColistF A xs) →
  ∀ {xs} → A xs → Colist xs
Colist-coind-ho' A h Axs =
  Colist-coind-stronger-ho A (λ Ays → inj₁ (h Ays)) Axs

-- The first-order version.
Colist-coind-stronger :
  (A : D → Set) →
  (∀ {xs} → A xs →
    (xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'))
    ∨ Colist xs) →
  ∀ {xs} → A xs → Colist xs
Colist-coind-stronger = Colist-coind-stronger-ho

------------------------------------------------------------------------------
-- References
--
-- Paulson, L. C. (1997). Mechanizing Coinduction and Corecursion in
-- Higher-order Logic. In: Journal of Logic and Computation 7.2,
-- pp. 175–204.
