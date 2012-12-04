------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesATP where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.List
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {fs} →
                        ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs' →
                        fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair-helper {fs} (.(true ∷ []) , fs' , nilF*T , h₁ , h₂) = prf
  where
  postulate prf : fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
  {-# ATP prove prf #-}

head-tail-Fair-helper {fs} (.(false ∷ ft) , fs' , fcons*T {ft} y , h₁ , h₂) = prf
  where
  postulate prf : fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
  {-# ATP prove prf #-}

postulate head-tail-Fair : ∀ {fs} → Fair fs → fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
{-# ATP prove head-tail-Fair head-tail-Fair-helper #-}

tail-Fair-helper : ∀ {fs} →
                   ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs' →
                   Fair (tail₁ fs)
tail-Fair-helper {fs} (.(true ∷ []) , fs' , nilF*T , Ffs' , h) = prf
  where
  postulate prf : Fair (tail₁ fs)
  {-# ATP prove prf #-}

tail-Fair-helper {fs} (.(false ∷ ft) , fs' , fcons*T {ft} FTft , Ffs' , h) = prf
  where
  postulate prf : Fair (tail₁ fs)
  {-# ATP prove prf Fair-gfp₃ #-}

postulate tail-Fair : ∀ {fs} → Fair fs → Fair (tail₁ fs)
{-# ATP prove tail-Fair tail-Fair-helper #-}
