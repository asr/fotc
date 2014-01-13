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
  Colist-out : ∀ {xs} →
               Colist xs →
               xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')

  -- The higher-order version.
  Colist-out-ho : ∀ {n} → Colist n → ColistF Colist n

  -- Colist is the greatest post-fixed point of ColistF, i.e.
  --
  -- ∀ A. A ≤ ColistF A ⇒ A ≤ Colist.
  Colist-coind :
    (A : D → Set) →
    -- A is post-fixed point of ColistF.
    (∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')) →
    -- Colist is greater than A.
    ∀ {xs} → A xs → Colist xs

  -- The higher-order version.
  Colist-coind-ho :
    (A : D → Set) →
    (∀ {xs} → A xs → ColistF A xs) →
    ∀ {xs} → A xs → Colist xs

------------------------------------------------------------------------------
-- Colist-out and Colist-out-ho are equivalents

Colist-out-fo : ∀ {xs} →
                Colist xs →
                xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')
Colist-out-fo = Colist-out-ho

Colist-out-ho' : ∀ {xs} → Colist xs → ColistF Colist xs
Colist-out-ho' = Colist-out

------------------------------------------------------------------------------
-- Colist-coind and Colist-coind-ho are equivalents

Colist-coind-fo :
  (A : D → Set) →
  (∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')) →
  ∀ {xs} → A xs → Colist xs
Colist-coind-fo = Colist-coind

Colist-coind-ho' :
  (A : D → Set) →
  (∀ {xs} → A xs → ColistF A xs) →
  ∀ {xs} → A xs → Colist xs
Colist-coind-ho' = Colist-coind

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Colist predicate is also a pre-fixed point of the functional ColistF,
-- i.e.
--
-- ColistF Colist ≤ Colist.
Colist-in : ∀ {xs} →
            xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs') →
            Colist xs
Colist-in h = Colist-coind A h' h
  where
  A : D → Set
  A xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')

  h' : ∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')
  h' (inj₁ xs≡0) = inj₁ xs≡0
  h' (inj₂ (x' , xs' , prf , CLxs' )) =
    inj₂ (x' , xs' , prf , Colist-out CLxs')

-- The higher-order version.
Colist-in-ho : ∀ {xs} → ColistF Colist xs → Colist xs
Colist-in-ho = Colist-in
