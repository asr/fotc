------------------------------------------------------------------------------
-- Fair properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair.PropertiesI where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Relation.Binary.EqReasoning
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

head-tail-Fair-helper : ∀ {fs ft fs'} → F*T ft → fs ≡ ft ++ fs' →
                        fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair-helper {fs} {fs' = fs'} nilF*T h = inj₁ prf₃
  where
  prf₁ : fs ≡ T ∷ [] ++ fs'
  prf₁ = fs              ≡⟨ h ⟩
         (T ∷ []) ++ fs' ≡⟨ ++-∷ T [] fs' ⟩
         T ∷ [] ++ fs' ∎

  prf₂ : tail₁ fs ≡ [] ++ fs'
  prf₂ = tail₁ fs              ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (T ∷ [] ++ fs') ≡⟨ tail-∷ T ([] ++ fs') ⟩
         [] ++ fs' ∎

  prf₃ : fs ≡ T ∷ tail₁ fs
  prf₃ = fs             ≡⟨ prf₁ ⟩
         T ∷ [] ++ fs'  ≡⟨ cong (_∷_ T) (sym prf₂) ⟩
         T ∷ tail₁ fs ∎

head-tail-Fair-helper {fs} {fs' = fs'} (consF*T {ft} FTft) h = inj₂ prf₃
  where
  prf₁ : fs ≡ F ∷ ft ++ fs'
  prf₁ = fs              ≡⟨ h ⟩
         (F ∷ ft) ++ fs' ≡⟨ ++-∷ F ft fs' ⟩
         F ∷ ft ++ fs' ∎

  prf₂ : tail₁ fs ≡ ft ++ fs'
  prf₂ = tail₁ fs              ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (F ∷ ft ++ fs') ≡⟨ tail-∷ F (ft ++ fs') ⟩
         ft ++ fs' ∎

  prf₃ : fs ≡ F ∷ tail₁ fs
  prf₃ = fs             ≡⟨ prf₁ ⟩
         F ∷ ft ++ fs'  ≡⟨ cong (_∷_ F) (sym prf₂) ⟩
         F ∷ tail₁ fs ∎

head-tail-Fair : ∀ {fs} → Fair fs → fs ≡ T ∷ tail₁ fs ∨ fs ≡ F ∷ tail₁ fs
head-tail-Fair {fs} Ffs = head-tail-Fair-helper FTft fs≡ol++fs'
  where
  unfold-fs : ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs'
  unfold-fs = Fair-gfp₁ Ffs

  ft : D
  ft = ∃-proj₁ unfold-fs

  fs' : D
  fs' = ∃-proj₁ (∃-proj₂ unfold-fs)

  FTft : F*T ft
  FTft = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-fs))

  fs≡ol++fs' : fs ≡ ft ++ fs'
  fs≡ol++fs' = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs)))

tail-Fair-helper : ∀ {fs ft fs'} → F*T ft → fs ≡ ft ++ fs' → Fair fs' →
                   Fair (tail₁ fs)
tail-Fair-helper {fs} {fs' = fs'} nilF*T h Ffs' = subst Fair (sym prf₂) Ffs'
  where
  prf₁ : fs ≡ T ∷ fs'
  prf₁ = fs              ≡⟨ h ⟩
         (T ∷ []) ++ fs' ≡⟨ ++-∷ T [] fs' ⟩
         T ∷ [] ++ fs'   ≡⟨ cong (_∷_ T) (++-[] fs') ⟩
         T ∷ fs' ∎

  prf₂ : tail₁ fs ≡ fs'
  prf₂ = tail₁ fs        ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (T ∷ fs') ≡⟨ tail-∷ T fs' ⟩
         fs' ∎

tail-Fair-helper {fs} {fs' = fs'} (consF*T {ft} FTft) h Ffs' =
  subst Fair (sym prf₂) (Fair-gfp₃ (ft , fs' , FTft , Ffs' , refl))
  where
  prf₁ : fs ≡ F ∷ ft ++ fs'
  prf₁ = fs              ≡⟨ h ⟩
         (F ∷ ft) ++ fs' ≡⟨ ++-∷ F ft fs' ⟩
         F ∷ ft ++ fs' ∎

  prf₂ : tail₁ fs ≡ ft ++ fs'
  prf₂ = tail₁ fs              ≡⟨ cong tail₁ prf₁ ⟩
         tail₁ (F ∷ ft ++ fs') ≡⟨ tail-∷ F (ft ++ fs') ⟩
         ft ++ fs' ∎

tail-Fair : ∀ {fs} → Fair fs → Fair (tail₁ fs)
tail-Fair {fs} Ffs = tail-Fair-helper FTft fs≡ol++fs' Ffs'
  where
  unfold-fs : ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs'
  unfold-fs = Fair-gfp₁ Ffs

  ft : D
  ft = ∃-proj₁ unfold-fs

  fs' : D
  fs' = ∃-proj₁ (∃-proj₂ unfold-fs)

  FTft : F*T ft
  FTft = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-fs))

  Ffs' : Fair fs'
  Ffs' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs)))

  fs≡ol++fs' : fs ≡ ft ++ fs'
  fs≡ol++fs' = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs)))
