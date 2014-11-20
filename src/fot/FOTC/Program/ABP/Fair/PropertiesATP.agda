------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.ABP.Fair.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the Fair
-- predicate is also a pre-fixed point of the functional FairF, i.e.
--
-- FairF Fair ≤ Fair (see FOTC.Program.ABP.Fair).
Fair-in : ∀ {os} → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os' →
          Fair os
Fair-in h = Fair-coind A h' h
  where
  A : D → Set
  A os = ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os'
  {-# ATP definition A #-}

  postulate
    h' : ∀ {os} → A os → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ A os'
  -- TODO (20 November 2014). See Apia issue 15.
  -- {-# ATP prove h' #-}

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos with Fair-out Fos
... | (.(T ∷ []) , os' , f*tnil , h , Fos') = prf
  where
  postulate prf : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf #-}

... | (.(F ∷ ft) , os' , f*tcons {ft} FTft , h , Fos') = prf
  where
  postulate prf : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf #-}

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos with Fair-out Fos
... | .(T ∷ []) , os' , f*tnil , h , Fos' = prf
  where
  postulate prf : Fair (tail₁ os)
  {-# ATP prove prf #-}
... | .(F ∷ ft) , os' , f*tcons {ft} FTft , h , Fos' = prf
  where
  postulate prf : Fair (tail₁ os)
  {-# ATP prove prf Fair-in #-}
