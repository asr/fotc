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
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the Fair
-- predicate is also a pre-fixed point of the functional FairF, i.e.
--
-- FairF Fair ≤ Fair (see FOTC.Program.ABP.Fair).
Fair-pre-fixed :
  ∀ {os} →
  ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os' →
  Fair os
Fair-pre-fixed h = Fair-coind A h' h
  where
  A : D → Set
  A os = ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os'

  h' : ∀ {os} → A os → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ A os'
  h' (ft , os' , FTft , prf , Fos') = ft , os' , FTft , prf , Fair-unf Fos'

head-tail-Fair : ∀ {os} → Fair os → os ≡ T ∷ tail₁ os ∨ os ≡ F ∷ tail₁ os
head-tail-Fair {os} Fos with Fair-unf Fos
... | .(true ∷ []) , os' , f*tnil , prf , Fos' = inj₁ prf₃
  where
  prf₁ : os ≡ T ∷ [] ++ os'
  prf₁ = os              ≡⟨ prf ⟩
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

... | .(false ∷ ft) , os' , f*tcons {ft} FTft , prf , Fos' =
  inj₂ prf₃
  where
  prf₁ : os ≡ F ∷ ft ++ os'
  prf₁ = os              ≡⟨ prf ⟩
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

tail-Fair : ∀ {os} → Fair os → Fair (tail₁ os)
tail-Fair {os} Fos with Fair-unf Fos
... | .(T ∷ []) , os' , f*tnil , prf , Fos' =
  subst Fair (sym prf₂) Fos'
  where
  prf₁ : os ≡ T ∷ os'
  prf₁ = os              ≡⟨ prf ⟩
         (T ∷ []) ++ os' ≡⟨ ++-∷ T [] os' ⟩
         T ∷ [] ++ os'   ≡⟨ ∷-rightCong (++-leftIdentity os') ⟩
         T ∷ os'         ∎

  prf₂ : tail₁ os ≡ os'
  prf₂ = tail₁ os        ≡⟨ tailCong prf₁ ⟩
         tail₁ (T ∷ os') ≡⟨ tail-∷ T os' ⟩
         os'             ∎

... | .(F ∷ ft) , os' , f*tcons {ft} FTft , prf , Fos' =
    subst Fair (sym prf₂) (Fair-pre-fixed (ft , os' , FTft , refl , Fos'))
  where
  prf₁ : os ≡ F ∷ ft ++ os'
  prf₁ = os              ≡⟨ prf ⟩
         (F ∷ ft) ++ os' ≡⟨ ++-∷ F ft os' ⟩
         F ∷ ft ++ os'   ∎

  prf₂ : tail₁ os ≡ ft ++ os'
  prf₂ = tail₁ os              ≡⟨ tailCong prf₁ ⟩
         tail₁ (F ∷ ft ++ os') ≡⟨ tail-∷ F (ft ++ os') ⟩
         ft ++ os'             ∎
