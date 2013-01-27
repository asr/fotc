------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {os} →
                        ∃[ ft ] ∃[ os' ] F*T ft ∧ Fair os' ∧ os ≡ ft ++ os' →
                        os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair-helper {os} (.(true ∷ []) , os' , f*tnil , h₁ , h₂) = prf
  where
  postulate prf : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf #-}

head-tail-Fair-helper {os} (.(false ∷ ft) , os' , f*tcons {ft} y , h₁ , h₂) = prf
  where
  postulate prf : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf #-}

postulate
  head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
{-# ATP prove head-tail-Fair head-tail-Fair-helper #-}

tail-Fair-helper : ∀ {os} →
                   ∃[ ft ] ∃[ os' ] F*T ft ∧ Fair os' ∧ os ≡ ft ++ os' →
                   Fair (tail₁ os)
tail-Fair-helper {os} (.(true ∷ []) , os' , f*tnil , Fos' , h) = prf
  where
  postulate prf : Fair (tail₁ os)
  {-# ATP prove prf #-}

tail-Fair-helper {os} (.(false ∷ ft) , os' , f*tcons {ft} FTft , Fos' , h) = prf
  where
  postulate prf : Fair (tail₁ os)
  {-# ATP prove prf Fair-pre-fixed #-}

postulate tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
{-# ATP prove tail-Fair tail-Fair-helper #-}
