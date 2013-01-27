------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {os} →
                        ∃[ ft ] ∃[ os' ] F*T ft ∧ Fair os' ∧ os ≡ ft ++ os' →
                        os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair-helper {os} (.(true ∷ []) , os' , f*tnil , h₁ , h₂) = inj₁ prf₃
  where
  prf₁ : os ≡ T ∷ [] ++ os'
  prf₁ = os              ≡⟨ h₂ ⟩
         (T ∷ []) ++ os' ≡⟨ ++-∷ T [] os' ⟩
         T ∷ [] ++ os'   ∎

  prf₂ : tail₁ os ≡ [] ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (T ∷ [] ++ os') ≡⟨ tail-∷ T ([] ++ os') ⟩
         [] ++ os'             ∎

  prf₃ : os ≡ T ∷ tail₁ os
  prf₃ = os             ≡⟨ prf₁ ⟩
         T ∷ [] ++ os'  ≡⟨ ∷-rightCong (sym prf₂) ⟩
         T ∷ tail₁ os   ∎

head-tail-Fair-helper {os} (.(false ∷ ft) , os' , f*tcons {ft} y , h₁ , h₂) =
  inj₂ prf₃
  where
  prf₁ : os ≡ F ∷ ft ++ os'
  prf₁ = os              ≡⟨ h₂ ⟩
         (F ∷ ft) ++ os' ≡⟨ ++-∷ F ft os' ⟩
         F ∷ ft ++ os'   ∎

  prf₂ : tail₁ os ≡ ft ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (F ∷ ft ++ os') ≡⟨ tail-∷ F (ft ++ os') ⟩
         ft ++ os'             ∎

  prf₃ : os ≡ F ∷ tail₁ os
  prf₃ = os             ≡⟨ prf₁ ⟩
         F ∷ ft ++ os'  ≡⟨ ∷-rightCong (sym prf₂) ⟩
         F ∷ tail₁ os   ∎

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos = head-tail-Fair-helper (Fair-unf Fos)

tail-Fair-helper : ∀ {os} →
                   ∃[ ft ] ∃[ os' ] F*T ft ∧ Fair os' ∧ os ≡ ft ++ os' →
                   Fair (tail₁ os)
tail-Fair-helper {os} (.(true ∷ []) , os' , f*tnil , Fos' , h) =
  subst Fair (sym prf₂) Fos'
  where
  prf₁ : os ≡ T ∷ os'
  prf₁ = os              ≡⟨ h ⟩
         (T ∷ []) ++ os' ≡⟨ ++-∷ T [] os' ⟩
         T ∷ [] ++ os'   ≡⟨ ∷-rightCong (++-leftIdentity os') ⟩
         T ∷ os'         ∎

  prf₂ : tail₁ os ≡ os'
  prf₂ = tail₁ os        ≡⟨ tailCong prf₁ ⟩
         tail₁ (T ∷ os') ≡⟨ tail-∷ T os' ⟩
         os'             ∎

tail-Fair-helper {os} (.(false ∷ ft) , os' , f*tcons {ft} FTft , Fos' , h) =
  subst Fair (sym prf₂) (Fair-pre-fixed (ft , os' , FTft , Fos' , refl))
  where
  prf₁ : os ≡ F ∷ ft ++ os'
  prf₁ = os              ≡⟨ h ⟩
         (F ∷ ft) ++ os' ≡⟨ ++-∷ F ft os' ⟩
         F ∷ ft ++ os'   ∎

  prf₂ : tail₁ os ≡ ft ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (F ∷ ft ++ os') ≡⟨ tail-∷ F (ft ++ os') ⟩
         ft ++ os'             ∎

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos = tail-Fair-helper (Fair-unf Fos)
