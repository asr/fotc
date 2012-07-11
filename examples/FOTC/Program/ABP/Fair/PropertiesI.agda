------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {fs} →
                        ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs' →
                        fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair-helper {fs} (.(true ∷ []) , fs' , nilF*T , h₁ , h₂) = inj₁ prf₃
  where
  prf₁ : fs ≡ T ∷ [] ++ fs'
  prf₁ = fs              ≡⟨ h₂ ⟩
         (T ∷ []) ++ fs' ≡⟨ ++-∷ T [] fs' ⟩
         T ∷ [] ++ fs'   ∎

  prf₂ : tail₁ fs ≡ [] ++ fs'
  prf₂ = tail₁ fs              ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (T ∷ [] ++ fs') ≡⟨ tail-∷ T ([] ++ fs') ⟩
         [] ++ fs'             ∎

  prf₃ : fs ≡ T ∷ tail₁ fs
  prf₃ = fs             ≡⟨ prf₁ ⟩
         T ∷ [] ++ fs'  ≡⟨ cong (_∷_ T) (sym prf₂) ⟩
         T ∷ tail₁ fs   ∎

head-tail-Fair-helper {fs} (.(false ∷ ft) , fs' , consF*T {ft} y , h₁ , h₂) =
  inj₂ prf₃
  where
  prf₁ : fs ≡ F ∷ ft ++ fs'
  prf₁ = fs              ≡⟨ h₂ ⟩
         (F ∷ ft) ++ fs' ≡⟨ ++-∷ F ft fs' ⟩
         F ∷ ft ++ fs'   ∎

  prf₂ : tail₁ fs ≡ ft ++ fs'
  prf₂ = tail₁ fs              ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (F ∷ ft ++ fs') ≡⟨ tail-∷ F (ft ++ fs') ⟩
         ft ++ fs'             ∎

  prf₃ : fs ≡ F ∷ tail₁ fs
  prf₃ = fs             ≡⟨ prf₁ ⟩
         F ∷ ft ++ fs'  ≡⟨ cong (_∷_ F) (sym prf₂) ⟩
         F ∷ tail₁ fs   ∎

head-tail-Fair : ∀ {fs} → Fair fs → fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair {fs} Ffs = head-tail-Fair-helper (Fair-gfp₁ Ffs)

tail-Fair-helper : ∀ {fs} →
                   ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs' →
                   Fair (tail₁ fs)
tail-Fair-helper {fs} (.(true ∷ []) , fs' , nilF*T , Ffs' , h) =
  subst Fair (sym prf₂) Ffs'
  where
  prf₁ : fs ≡ T ∷ fs'
  prf₁ = fs              ≡⟨ h ⟩
         (T ∷ []) ++ fs' ≡⟨ ++-∷ T [] fs' ⟩
         T ∷ [] ++ fs'   ≡⟨ cong (_∷_ T) (++-[] fs') ⟩
         T ∷ fs'         ∎

  prf₂ : tail₁ fs ≡ fs'
  prf₂ = tail₁ fs        ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (T ∷ fs') ≡⟨ tail-∷ T fs' ⟩
         fs'             ∎

tail-Fair-helper {fs} (.(false ∷ ft) , fs' , consF*T {ft} FTft , Ffs' , h) =
  subst Fair (sym prf₂) (Fair-gfp₃ (ft , fs' , FTft , Ffs' , refl))
  where
  prf₁ : fs ≡ F ∷ ft ++ fs'
  prf₁ = fs              ≡⟨ h ⟩
         (F ∷ ft) ++ fs' ≡⟨ ++-∷ F ft fs' ⟩
         F ∷ ft ++ fs'   ∎

  prf₂ : tail₁ fs ≡ ft ++ fs'
  prf₂ = tail₁ fs              ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (F ∷ ft ++ fs') ≡⟨ tail-∷ F (ft ++ fs') ⟩
         ft ++ fs'             ∎

tail-Fair : ∀ {fs} → Fair fs → Fair (tail₁ fs)
tail-Fair {fs} Ffs = tail-Fair-helper (Fair-gfp₁ Ffs)
