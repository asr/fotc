------------------------------------------------------------------------------
-- Co-lists
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas     #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module GFPs.Colist where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- Colist is a greatest fixed-point of a functor

-- The functor.
ListF : (D → Set) → D → Set
ListF A xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')

-- Colist is the greatest fixed-point of ListF.
postulate
  Colist : D → Set

  -- Colist is a post-fixed point of ListF, i.e.
  --
  -- Colist ≤ ListF Colist.
  Colist-out-ho : ∀ {n} → Colist n → ListF Colist n

  -- Colist is the greatest post-fixed point of ListF, i.e.
  --
  -- ∀ A. A ≤ ListF A ⇒ A ≤ Colist.
  Colist-coind-ho :
    (A : D → Set) →
    -- A is post-fixed point of ListF.
    (∀ {xs} → A xs → ListF A xs) →
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
-- Colist predicate is also a pre-fixed point of the functional ListF,
-- i.e.
--
-- ListF Colist ≤ Colist.
Colist-in-ho : ∀ {xs} → ListF Colist xs → Colist xs
Colist-in-ho h = Colist-coind-ho A h' h
  where
  A : D → Set
  A xs = ListF Colist xs

  h' : ∀ {xs} → A xs → ListF A xs
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
    (∀ {xs} → A xs → ListF A xs ∨ Colist xs) →
    ∀ {xs} → A xs → Colist xs

Colist-coind-ho' :
  (A : D → Set) →
  (∀ {xs} → A xs → ListF A xs) →
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

-- 13 January 2014. As expected, we cannot prove
-- Colist-coind-stronger-ho from Colist-coind-ho.
Colist-coind-stronger-ho' :
  (A : D → Set) →
  (∀ {xs} → A xs → ListF A xs ∨ Colist xs) →
  ∀ {xs} → A xs → Colist xs
Colist-coind-stronger-ho' A h {xs} Axs = case prf (λ h' → h') (h Axs)
  where
  prf : ListF A xs → Colist xs
  prf h' = Colist-coind-ho A {!!} Axs

------------------------------------------------------------------------------
-- References
--
-- Paulson, L. C. (1997). Mechanizing Coinduction and Corecursion in
-- Higher-order Logic. Journal of Logic and Computation 7.2,
-- pp. 175–204.
