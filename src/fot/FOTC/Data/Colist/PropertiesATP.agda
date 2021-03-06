------------------------------------------------------------------------------
-- Colist properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Colist.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Colist

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Colist predicate is also a pre-fixed point of the functional
-- ColistF, i.e.
--
-- ColistF Colist ≤ Colist (see FOTC.Data.Colist.Type).

-- See Issue https://github.com/asr/apia/issues/81 .
A : D → Set
A xs =   xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')
{-# ATP definition A #-}

Colist-in :
  ∀ {xs} →
  xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs') →
  Colist xs
Colist-in h = Colist-coind A h' h
  where
  postulate
    h' : ∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')
  {-# ATP prove h' #-}
