------------------------------------------------------------------------------
-- Colist properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Colist.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Colist

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Colist predicate is also a pre-fixed point of the functional
-- ColistF, i.e.
--
-- ColistF Colist ≤ Colist (see Interactive.FOTC.Data.Colist.Type).
Colist-in :
  ∀ {xs} →
  xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs') →
  Colist xs
Colist-in h = Colist-coind A h' h
  where
  A : D → Set
  A xs =   xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')

  h' : ∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')
  h' (inj₁ xs≡[])                    = inj₁ xs≡[]
  h' (inj₂ (x' , xs' , prf , Clxs')) = inj₂ (x' , xs' , prf , Colist-out Clxs')
