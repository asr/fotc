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

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos with Fair-unf Fos
... | (.(true ∷ []) , os' , f*tnil , prf , Fos') = prf₁
  where
  postulate prf₁ : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf₁ #-}

... | (.(false ∷ ft) , os' , f*tcons {ft} y , prf , Fos') = prf₁
  where
  postulate prf₁ : os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
  {-# ATP prove prf₁ #-}

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos with Fair-unf Fos
... | .(true ∷ []) , os' , f*tnil , prf , Fos' = prf₁
  where
  postulate prf₁ : Fair (tail₁ os)
  {-# ATP prove prf₁ #-}

... | .(false ∷ ft) , os' , f*tcons {ft} FTft , prf , Fos' = prf₁
  where
  postulate prf₁ : Fair (tail₁ os)
  {-# ATP prove prf₁ Fair-pre-fixed #-}
